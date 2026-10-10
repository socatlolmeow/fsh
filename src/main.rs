use std::borrow::Cow;
use std::cell::OnceCell;
use std::collections::{BTreeSet, HashMap};
use std::env;
use std::fs::{self, File, OpenOptions};
use std::io::ErrorKind;
use std::os::unix::fs::PermissionsExt;
use std::os::unix::process::ExitStatusExt;
use std::process::{Child, ChildStdout, Command, Stdio};

use rustyline::completion::{Completer, FilenameCompleter, Pair};
use rustyline::error::ReadlineError;
use rustyline::highlight::Highlighter;
use rustyline::hint::{Hinter, HistoryHinter};
use rustyline::history::{FileHistory};
use rustyline::validate::Validator;
use rustyline::{CompletionType, Config, Context, Editor, Helper};

const BUILTINS: [&str; 9] = [
    "cd", "pwd", "exit", "export", "unset", "alias", "unalias", "source", "history",
];

const DEFAULT_PROMPT: &str = "\\e[1;34m%d\\e[0m%g %c❯%r ";

enum Tok {
    Word(String, bool),
    Pipe,
    And,
    Or,
    Semi,
    In,
    Out,
    Append,
}

#[derive(Default)]
struct Cmd {
    args: Vec<String>,
    stdin: Option<String>,
    stdout: Option<(String, bool)>, // (path, append)
}

#[derive(Clone, Copy)]
enum Conn {
    Always,
    And,
    Or,
}

struct Item {
    conn: Conn,
    pipeline: Vec<Cmd>,
}

fn is_op(c: char) -> bool {
    matches!(c, '|' | '&' | ';' | '<' | '>')
}

fn home() -> String {
    env::var("HOME").unwrap_or_else(|_| "/".into())
}

fn parse(toks: Vec<Tok>) -> Result<Vec<Item>, String> {
    let mut items = Vec::new();
    let mut pipeline = Vec::new();
    let mut cmd = Cmd::default();
    let mut conn = Conn::Always;
    let mut redir: Option<Tok> = None;

    for tok in toks {
        match tok {
            Tok::Word(w, glob) => match redir.take() {
                Some(Tok::In) => cmd.stdin = Some(w),
                Some(Tok::Out) => cmd.stdout = Some((w, false)),
                Some(Tok::Append) => cmd.stdout = Some((w, true)),
                _ if glob => cmd.args.extend(expand_glob(&w)),
                _ => cmd.args.push(w),
            },
            Tok::In | Tok::Out | Tok::Append => {
                if redir.is_some() {
                    return Err("syntax error near redirection".into());
                }
                redir = Some(tok);
            }
            Tok::Pipe | Tok::And | Tok::Or | Tok::Semi => {
                if redir.is_some() {
                    return Err("expected a file after redirection".into());
                }
                if cmd.args.is_empty() {
                    return Err("syntax error: expected a command".into());
                }
                pipeline.push(std::mem::take(&mut cmd));
                if !matches!(tok, Tok::Pipe) {
                    items.push(Item { conn, pipeline: std::mem::take(&mut pipeline) });
                    conn = match tok {
                        Tok::And => Conn::And,
                        Tok::Or => Conn::Or,
                        _ => Conn::Always,
                    };
                }
            }
        }
    }

    if redir.is_some() {
        return Err("expected a file after redirection".into());
    }
    if cmd.args.is_empty() {
        if !pipeline.is_empty() || !matches!(conn, Conn::Always) {
            return Err("syntax error: expected a command".into());
        }
    } else {
        pipeline.push(cmd);
        items.push(Item { conn, pipeline });
    }
    Ok(items)
}

fn wildmatch(p: &[char], t: &[char]) -> bool {
    match p.first() {
        None => t.is_empty(),
        Some('*') => (0..=t.len()).any(|k| wildmatch(&p[1..], &t[k..])),
        Some('?') => !t.is_empty() && wildmatch(&p[1..], &t[1..]),
        Some(c) => t.first() == Some(c) && wildmatch(&p[1..], &t[1..]),
    }
}

fn expand_glob(pat: &str) -> Vec<String> {
    let (dir, file) = match pat.rfind('/') {
        Some(i) => (&pat[..=i], &pat[i + 1..]),
        None => ("", pat),
    };
    if dir.contains(['*', '?']) {
        return vec![pat.to_string()];
    }
    let rd = match fs::read_dir(if dir.is_empty() { "." } else { dir }) {
        Ok(rd) => rd,
        Err(_) => return vec![pat.to_string()],
    };
    let p: Vec<char> = file.chars().collect();
    let mut out: Vec<String> = rd
        .flatten()
        .filter_map(|e| {
            let name = e.file_name().to_string_lossy().into_owned();
            if name.starts_with('.') && !file.starts_with('.') {
                return None;
            }
            let t: Vec<char> = name.chars().collect();
            wildmatch(&p, &t).then(|| format!("{dir}{name}"))
        })
        .collect();
    if out.is_empty() {
        return vec![pat.to_string()];
    }
    out.sort();
    out
}

fn split_assign(s: &str) -> Option<(&str, &str)> {
    let (k, v) = s.split_once('=')?;
    let ok = !k.is_empty()
        && !k.starts_with(|c: char| c.is_ascii_digit())
        && k.chars().all(|c| c.is_ascii_alphanumeric() || c == '_');
    ok.then_some((k, v))
}


fn short_cwd() -> String {
    let cwd = env::current_dir()
        .map(|p| p.display().to_string())
        .unwrap_or_else(|_| "?".into());
    let home = home();
    match cwd.strip_prefix(&home) {
        Some("") => "~".into(),
        Some(rest) if rest.starts_with('/') => format!("~{rest}"),
        _ => cwd.clone(),
    }
}

fn git_branch() -> Option<String> {
    let mut dir = env::current_dir().ok()?;
    loop {
        if let Ok(head) = fs::read_to_string(dir.join(".git/HEAD")) {
            let head = head.trim();
            return Some(match head.strip_prefix("ref: refs/heads/") {
                Some(branch) => branch.to_string(),
                None => head.chars().take(7).collect(),
            });
        }
        if !dir.pop() {
            return None;
        }
    }
}

struct Shell {
    aliases: HashMap<String, String>,
    prev_dir: Option<String>,
    status: i32,
    running: bool,
}

impl Shell {
    fn new() -> Self {
        Shell { aliases: HashMap::new(), prev_dir: None, status: 0, running: true }
    }

    fn prompt(&self) -> String {
        let tpl = env::var("FSH_PROPT").unwrap_or_else(|_| DEFAULT_PROMPT.into());
        let tpl = tpl.replace("\\e", "\x1b");
        let mut out = String::new();
        let mut it = tpl.chars();
        while let Some(c) = it.next() {
            if c != '%' {
                out.push(c);
                continue;
            }
            match it.next() {
                Some('d') => out.push_str(&short_cwd()),
                Some('g') => {
                    if let Some(b) = git_branch() {
                        out.push_str(&format!(" \x1b[35m{b}\x1b[0m"));
                    }
                }
                Some('?') => {
                    if self.status != 0 {
                        out.push_str(&self.status.to_string());
                    }
                }
                Some('c') => out.push_str(if self.status == 0 { "\x1b[32m" } else { "\x1b[31m" }),
                Some('r') => out.push_str("\x1b[0m"),
                Some('%') => out.push('%'),
                Some(other) => {
                    out.push('%');
                    out.push(other);
                }
                None => out.push('%'),
            }
        }
        out
    }

    fn expand_var(&self, s: &[char], i: &mut usize, out: &mut String) {
        // s[*i] == '$'
        let name: String;
        match s.get(*i + 1) {
            Some('?') => {
                out.push_str(&self.status.to_string());
                *i += 2;
                return;
            }
            Some('{') => match s[*i + 2..].iter().position(|&c| c == '}') {
                Some(end) => {
                    name = s[*i + 2..*i + 2 + end].iter().collect();
                    *i += end + 3;
                }
                None => {
                    out.push('$');
                    *i += 1;
                    return;
                }
            },
            Some(&c) if c.is_alphabetic() || c == '_' => {
                let mut j = *i + 1;
                while j < s.len() && (s[j].is_alphanumeric() || s[j] == '_') {
                    j += 1;
                }
                name = s[*i + 1..j].iter().collect();
                *i = j;
            }
            _ => {
                out.push('$');
                *i += 1;
                return;
            }
        }
        out.push_str(&env::var(&name).unwrap_or_default());
    }

    fn lex(&self, input: &str) -> Result<Vec<Tok>, String> {
        let s: Vec<char> = input.chars().collect();
        let mut toks = Vec::new();
        let mut i = 0;

        while i < s.len() {
            let c = s[i];
            let next = s.get(i + 1).copied();
            match c {
                c if c.is_whitespace() => i += 1,
                '#' => break,
                '|' if next == Some('|') => {
                    toks.push(Tok::Or);
                    i += 2;
                }
                '|' => {
                    toks.push(Tok::Pipe);
                    i += 1;
                }
                '&' if next == Some('&') => {
                    toks.push(Tok::And);
                    i += 2;
                }
                '&' => return Err("background jobs (&) are not supported".into()),
                ';' => {
                    toks.push(Tok::Semi);
                    i += 1;
                }
                '<' => {
                    toks.push(Tok::In);
                    i += 1;
                }
                '>' if next == Some('>') => {
                    toks.push(Tok::Append);
                    i += 2;
                }
                '>' => {
                    toks.push(Tok::Out);
                    i += 1;
                }
                _ => {
                    let mut word = String::new();
                    let mut glob = false;
                    let start = i;
                    while i < s.len() && !s[i].is_whitespace() && !is_op(s[i]) {
                        match s[i] {
                            '\'' => {
                                i += 1;
                                while i < s.len() && s[i] != '\'' {
                                    word.push(s[i]);
                                    i += 1;
                                }
                                if i >= s.len() {
                                    return Err("unterminated quote".into());
                                }
                                i += 1;
                            }
                            '"' => {
                                i += 1;
                                loop {
                                    match s.get(i) {
                                        None => return Err("unterminated quote".into()),
                                        Some('"') => {
                                            i += 1;
                                            break;
                                        }
                                        Some('\\')
                                            if matches!(s.get(i + 1), Some('"' | '\\' | '$')) =>
                                        {
                                            word.push(s[i + 1]);
                                            i += 2;
                                        }
                                        Some('$') => self.expand_var(&s, &mut i, &mut word),
                                        Some(&ch) => {
                                            word.push(ch);
                                            i += 1;
                                        }
                                    }
                                }
                            }
                            '\\' => {
                                if let Some(&ch) = s.get(i + 1) {
                                    word.push(ch);
                                }
                                i += 2;
                            }
                            '$' => self.expand_var(&s, &mut i, &mut word),
                            '~' if i == start
                                && s.get(i + 1)
                                    .map_or(true, |&n| n == '/' || n.is_whitespace() || is_op(n)) =>
                            {
                                word.push_str(&home());
                                i += 1;
                            }
                            '*' | '?' => {
                                glob = true;
                                word.push(s[i]);
                                i += 1;
                            }
                            ch => {
                                word.push(ch);
                                i += 1;
                            }
                        }
                    }
                    toks.push(Tok::Word(word, glob));
                }
            }
        }
        Ok(toks)
    }

    fn run_line(&mut self, line: &str) {
        let items = match self.lex(line).and_then(parse) {
            Ok(items) => items,
            Err(e) => {
                eprintln!("fsh: {e}");
                self.status = 2;
                return;
            }
        };
        for Item { conn, pipeline } in items {
            match conn {
                Conn::And if self.status != 0 => continue,
                Conn::Or if self.status == 0 => continue,
                _ => {}
            }
            self.status = self.run_pipeline(pipeline);
            if !self.running {
                break;
            }
        }
    }

    fn apply_alias(&self, cmd: &mut Cmd) {
        let Some(val) = self.aliases.get(&cmd.args[0]) else { return };
        if let Ok(toks) = self.lex(val) {
            let mut new: Vec<String> = toks
                .into_iter()
                .filter_map(|t| if let Tok::Word(w, _) = t { Some(w) } else { None })
                .collect();
            if !new.is_empty() {
                new.extend(cmd.args.drain(1..));
                cmd.args = new;
            }
        }
    }

    fn run_pipeline(&mut self, mut cmds: Vec<Cmd>) -> i32 {
        for c in cmds.iter_mut() {
            self.apply_alias(c);
        }

        if cmds.len() == 1 && cmds[0].stdin.is_none() && cmds[0].stdout.is_none() {
            let args = cmds[0].args.clone();
            if let Some(status) = self.builtin(&args) {
                return status;
            }
        }

        let n = cmds.len();
        let mut children: Vec<Child> = Vec::new();
        let mut prev: Option<ChildStdout> = None;
        let mut status = 0;
        let mut spawned_last = false;

        for (i, cmd) in cmds.iter().enumerate() {
            let mut p = Command::new(&cmd.args[0]);
            p.args(&cmd.args[1..]);

            match (&cmd.stdin, prev.take()) {
                (Some(path), _) => match File::open(path) {
                    Ok(f) => {
                        p.stdin(f);
                    }
                    Err(e) => {
                        eprintln!("fsh: {path}: {e}");
                        status = 1;
                        continue;
                    }
                },
                (None, Some(out)) => {
                    p.stdin(out);
                }
                (None, None) => {
                    if i > 0 {
                        p.stdin(Stdio::null());
                    }
                }
            }

            if let Some((path, append)) = &cmd.stdout {
                let file = OpenOptions::new()
                    .write(true)
                    .create(true)
                    .append(*append)
                    .truncate(!*append)
                    .open(path);
                match file {
                    Ok(f) => {
                        p.stdout(f);
                    }
                    Err(e) => {
                        eprintln!("fsh: {path}: {e}");
                        status = 1;
                        continue;
                    }
                }
            } else if i < n - 1 {
                p.stdout(Stdio::piped());
            }

            match p.spawn() {
                Ok(mut child) => {
                    if i < n - 1 && cmd.stdout.is_none() {
                        prev = child.stdout.take();
                    }
                    children.push(child);
                    if i == n - 1 {
                        spawned_last = true;
                    }
                }
                Err(e) => {
                    let (msg, code) = match e.kind() {
                        ErrorKind::NotFound => ("command not found".to_string(), 127),
                        ErrorKind::PermissionDenied => ("permission denied".to_string(), 126),
                        _ => (e.to_string(), 126),
                    };
                    eprintln!("fsh: {}: {msg}", cmd.args[0]);
                    status = code;
                }
            }
        }

        let mut last = None;
        let mut interrupted = false;
        for mut child in children {
            if let Ok(s) = child.wait() {
                interrupted |= s.signal() == Some(libc::SIGINT);
                last = Some(s.code().unwrap_or_else(|| 128 + s.signal().unwrap_or(0)));
            }
        }
        if interrupted {
            eprintln!();
        }
        if spawned_last {
            if let Some(s) = last {
                status = s;
            }
        }
        status
    }


    fn builtin(&mut self, args: &[String]) -> Option<i32> {
        // bare `NAME=value`
        if args.len() == 1 {
            if let Some((k, v)) = split_assign(&args[0]) {
                unsafe {
                    env::set_var(k, v);
                }
                return Some(0);
            }
        }
        let rest = &args[1..];
        Some(match args[0].as_str() {
            "cd" => self.cd(rest.first().map(String::as_str)),
            "pwd" => {
                let cwd = env::current_dir().map(|p| p.display().to_string()).unwrap_or_default();
                println!("{cwd}");
                0
            }
            "exit" => {
                self.status = rest.first().and_then(|s| s.parse().ok()).unwrap_or(self.status);
                self.running = false;
                self.status
            }
            "export" => {
                for a in rest {
                    if let Some((k, v)) = split_assign(a) {
                        unsafe {
                        env::set_var(k, v);
                        }
                    }
                }
                0
            }
            "unset" => {
                for a in rest {
                    unsafe {
                    env::remove_var(a);
                    }
                }
                0
            }
            "alias" => self.alias(rest),
            "unalias" => {
                for a in rest {
                    self.aliases.remove(a);
                }
                0
            }
            "source" | "." => match rest.first() {
                Some(path) => self.source(path),
                None => {
                    eprintln!("fsh: source: missing file");
                    1
                }
            },
            _ => return None,
        })
    }

    fn cd(&mut self, arg: Option<&str>) -> i32 {
        let target = match arg {
            None => home(),
            Some("-") => match &self.prev_dir {
                Some(p) => p.clone(),
                None => {
                    eprintln!("fsh: cd: no previous directory");
                    return 1;
                }
            },
            Some(p) => p.to_string(),
        };
        let old = env::current_dir().ok().map(|p| p.display().to_string());
        match env::set_current_dir(&target) {
            Ok(()) => {
                if arg == Some("-") {
                    println!("{target}");
                }
                self.prev_dir = old;
                0
            }
            Err(e) => {
                eprintln!("fsh: cd: {target}: {e}");
                1
            }
        }
    }

    fn alias(&mut self, args: &[String]) -> i32 {
        if args.is_empty() {
            let mut all: Vec<_> = self.aliases.iter().collect();
            all.sort();
            for (k, v) in all {
                println!("alias {k}='{v}'");
            }
            return 0;
        }
        for a in args {
            match a.split_once('=') {
                Some((k, v)) => {
                    self.aliases.insert(k.to_string(), v.to_string());
                }
                None => match self.aliases.get(a) {
                    Some(v) => println!("alias {a}='{v}'"),
                    None => {
                        eprintln!("fsh: alias: {a}: not found");
                        return 1;
                    }
                },
            }
        }
        0
    }

    fn source(&mut self, path: &str) -> i32 {
        match fs::read_to_string(path) {
            Ok(text) => {
                for line in text.lines() {
                    if !self.running {
                        break;
                    }
                    let line = line.trim();
                    if line.is_empty() || line.starts_with('#') {
                        continue;
                    }
                    self.run_line(line);
                }
                0
            }
            Err(e) => {
                eprintln!("fsh: source: {path}: {e}");
                1
            }
        }
    }

    fn load_rc(&mut self) {
        let rc = format!("{}/.fshrc", home());
        if fs::metadata(&rc).is_ok() {
            self.source(&rc);
            self.status = 0;
        }
    }
}

fn path_commands() -> Vec<String> {
    let mut set = BTreeSet::new();
    for dir in env::split_paths(&env::var_os("PATH").unwrap_or_default()) {
        let Ok(rd) = fs::read_dir(dir) else { continue };
        for e in rd.flatten() {
            // fs::metadata follows symlinks (DirEntry::metadata does not)
            if let Ok(m) = fs::metadata(e.path()) {
                if m.is_file() && m.permissions().mode() & 0o111 != 0 {
                    set.insert(e.file_name().to_string_lossy().into_owned());
                }
            }
        }
    }
    for b in BUILTINS {
        set.insert(b.to_string());
    }
    set.into_iter().collect()
}

struct FshHelper {
    files: FilenameCompleter,
    hinter: HistoryHinter,
    cmds: OnceCell<Vec<String>>,
}

impl FshHelper {
    fn new() -> Self {
        FshHelper {
            files: FilenameCompleter::new(),
            hinter: HistoryHinter::new(),
            cmds: OnceCell::new(),
        }
    }
}

impl Completer for FshHelper {
    type Candidate = Pair;

    fn complete(
        &self,
        line: &str,
        pos: usize,
        ctx: &Context<'_>,
    ) -> rustyline::Result<(usize, Vec<Pair>)> {
        let before = &line[..pos];
        let start = before
            .rfind(|c: char| c == ' ' || c == '\t' || "|;&".contains(c))
            .map_or(0, |i| i + 1);
        let word = &before[start..];
        let head = before[..start].trim_end();
        let at_cmd = head.is_empty() || head.ends_with(['|', ';', '&']);

        if at_cmd && !word.contains('/') {
            let cmds = self.cmds.get_or_init(path_commands);
            let out: Vec<Pair> = cmds
                .iter()
                .filter(|c| c.starts_with(word))
                .map(|c| Pair { display: c.clone(), replacement: c.clone() })
                .collect();
            return Ok((start, out));
        }
        self.files.complete(line, pos, ctx)
    }
}

impl Hinter for FshHelper {
    type Hint = String;

    fn hint(&self, line: &str, pos: usize, ctx: &Context<'_>) -> Option<String> {
        self.hinter.hint(line, pos, ctx)
    }
}

impl Highlighter for FshHelper {
    fn highlight_hint<'h>(&self, hint: &'h str) -> Cow<'h, str> {
        Cow::Owned(format!("\x1b[90m{hint}\x1b[0m"))
    }
}

impl Validator for FshHelper {}
impl Helper for FshHelper {}

// handlers (! SIG_IGN) are reset on exec, so children die on C-c
// while the shell survive
extern "C" fn on_sigint(_: libc::c_int) {}

fn repl(mut shell: Shell) -> ! {
    let config = Config::builder().completion_type(CompletionType::List).build();
    let mut rl = match Editor::<FshHelper, FileHistory>::with_config(config) {
        Ok(rl) => rl,
        Err(e) => {
            eprintln!("fsh: {e}");
            std::process::exit(1);
        }
    };
    rl.set_helper(Some(FshHelper::new()));

    let hist = format!("{}/.fsh_history", home());
    let _ = rl.load_history(&hist);
    shell.load_rc();

    while shell.running {
        match rl.readline(&shell.prompt()) {
            Ok(input) => {
                let line = input.trim();
                if line.is_empty() {
                    continue;
                }
                let _ = rl.add_history_entry(line);
                if line == "history" {
                    for (i, entry) in rl.history().iter().enumerate() {
                        println!("{:>5}  {entry}", i + 1);
                    }
                    continue;
                }
                shell.run_line(line);
            }
            Err(ReadlineError::Interrupted) => shell.status = 130,
            Err(ReadlineError::Eof) => break,
            Err(e) => {
                eprintln!("fsh: {e}");
                break;
            }
        }
    }

    let _ = rl.save_history(&hist);
    std::process::exit(shell.status);
}

fn main() {
    unsafe {
        libc::signal(libc::SIGINT, on_sigint as *const () as libc::sighandler_t);
    }

    let args: Vec<String> = env::args().skip(1).collect();
    let mut shell = Shell::new();

    match args.as_slice() {
        [flag, cmd] if flag == "-c" => {
            shell.run_line(cmd);
            std::process::exit(shell.status);
        }
        [file] => {
            if shell.source(file) != 0 {
                shell.status = 1;
            }
            std::process::exit(shell.status);
        }
        _ => repl(shell),
    }
}
