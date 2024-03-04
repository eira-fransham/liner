use std::{fmt, io::{self, stdin, stdout}};
use termion::{
    event::Key,
    input::{Keys, TermRead},
    raw::{IntoRawMode, RawTerminal},
};

use super::*;
use crate::editor::Prompt;
use keymap;

pub type ColorClosure = Box<dyn Fn(&str) -> String>;

/// The default for `Context.word_divider_fn`.
pub fn get_buffer_words(buf: &Buffer) -> Vec<(usize, usize)> {
    let mut res = Vec::new();

    let mut word_start = None;
    let mut just_had_backslash = false;

    for (i, &c) in buf.chars().enumerate() {
        if c == '\\' {
            just_had_backslash = true;
            continue;
        }

        if let Some(start) = word_start {
            if c == ' ' && !just_had_backslash {
                res.push((start, i));
                word_start = None;
            }
        } else if c != ' ' {
            word_start = Some(i);
        }

        just_had_backslash = false;
    }

    if let Some(start) = word_start {
        res.push((start, buf.num_chars()));
    }

    res
}

/// The key bindings to use.
#[derive(Default, Copy, Clone, PartialEq, Eq, Hash, Debug)]
pub enum KeyBindings {
    Vi,
    #[default]
    Emacs,
}

#[derive(Default, Copy, Clone, PartialEq, Eq, Hash, Debug)]
pub struct DefaultTty;

pub trait TtyOut: io::Write {
    fn width(&self) -> io::Result<usize>;
}

impl TtyOut for RawTerminal<io::Stdout> {
    fn width(&self) -> io::Result<usize> {
        util::terminal_width()
    }
}

pub trait Tty {
    type Stdin: Iterator<Item = io::Result<Key>>;
    type Stdout: TtyOut;

    fn stdin(&mut self) -> Self::Stdin;
    fn stdout(&mut self) -> io::Result<Self::Stdout>;
}

impl Tty for DefaultTty {
    type Stdin = Keys<io::Stdin>;
    type Stdout = RawTerminal<io::Stdout>;

    fn stdin(&mut self) -> Self::Stdin {
        stdin().keys()
    }

    fn stdout(&mut self) -> io::Result<Self::Stdout> {
        stdout().into_raw_mode()
    }
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct Context<T = DefaultTty, F = Box<dyn Fn(&Buffer) -> Vec<(usize, usize)>>> {
    pub history: History,
    pub word_divider_fn: F,
    pub key_bindings: KeyBindings,
    pub terminal: T,
    pub buffer: String,
}

pub trait EditorContext: fmt::Write {
    type Terminal: Tty;
    type WordDividerIter: ExactSizeIterator<Item = (usize, usize)> + Clone;

    /// Get an immutable reference to the context history
    fn history(&self) -> &History;
    /// Get a mutable reference to the context history
    fn history_mut(&mut self) -> &mut History;
    /// Get the word divider points in the specified buffer
    fn word_divider(&self, buf: &Buffer) -> Self::WordDividerIter;
    /// Get an immutable reference to the output terminal
    fn terminal(&self) -> &Self::Terminal;
    /// Get a mutable reference to the output terminal
    fn terminal_mut(&mut self) -> &mut Self::Terminal;
    /// Get the key binding type (Vi or Emacs)
    fn key_bindings(&self) -> KeyBindings;

    /// Creates an `Editor` and feeds it keypresses from stdin until the line is entered.
    /// The output is stdout.
    /// The returned line has the newline removed.
    /// Before returning, will revert all changes to the history buffers.
    fn read_line<C: Completer>(
        &mut self,
        prompt: Prompt,
        f: Option<ColorClosure>,
        handler: &mut C,
    ) -> io::Result<String> where Self: Sized {
        self.read_line_with_init_buffer(prompt, handler, f, Buffer::new())
    }

    /// Same as `Context.read_line()`, but passes the provided initial buffer to the editor.
    ///
    /// ```no_run
    /// use liner::{Context, Completer, Prompt, EditorContext};
    ///
    /// struct EmptyCompleter;
    ///
    /// impl Completer for EmptyCompleter {
    ///     fn completions(&mut self, _start: &str) -> Vec<String> {
    ///         Vec::new()
    ///     }
    /// }
    ///
    /// let mut context = Context::new();
    /// let line =
    ///     context.read_line_with_init_buffer(Prompt::from("[prompt]$ "),
    ///                                        &mut EmptyCompleter,
    ///                                        Some(Box::new(|s| String::from(s))),
    ///                                        "some initial buffer");
    /// ```
    fn read_line_with_init_buffer<B: Into<Buffer>, C: Completer>(
        mut self,
        prompt: Prompt,
        handler: &mut C,
        f: Option<ColorClosure>,
        buffer: B,
    ) -> io::Result<String>
    where
        Self: Sized,
    {
        let keybindings = self.key_bindings();
        let stdin = self.terminal_mut().stdin();

        let ed = Editor::new_with_init_buffer(prompt, f, self, buffer)?;

        match keybindings {
            KeyBindings::Emacs => Self::handle_keys(stdin, keymap::Emacs::new(), ed, handler),
            KeyBindings::Vi => Self::handle_keys(stdin, keymap::Vi::new(), ed, handler),
        }

        // TODO: Why is this commented?
        //self.revert_all_history();
    }

    fn handle_keys<M: KeyMap, C: Completer>(
        stdin: <Self::Terminal as Tty>::Stdin,
        mut keymap: M,
        mut ed: Editor<Self>,
        handler: &mut C,
    ) -> io::Result<String>
    where
        Self: Sized,
    {
        keymap.init(&mut ed)?;
        for c in stdin {
            if keymap.handle_key(c?, &mut ed, handler)? {
                break;
            }
        }

        Ok(ed.into())
    }

    fn revert_all_history(&mut self) {
        for buf in &mut self.history_mut().buffers {
            buf.revert();
        }
    }
}

impl<C: EditorContext> EditorContext for &'_ mut C {
    type Terminal = C::Terminal;
    type WordDividerIter = C::WordDividerIter;

    fn history(&self) -> &History {
        (&**self).history()
    }

    fn history_mut(&mut self) -> &mut History {
        (&mut **self).history_mut()
    }

    fn word_divider(&self, buf: &Buffer) -> Self::WordDividerIter {
        (&**self).word_divider(buf)
    }

    fn terminal(&self) -> &Self::Terminal {
        (&**self).terminal()
    }

    fn terminal_mut(&mut self) -> &mut Self::Terminal {
        (&mut **self).terminal_mut()
    }

    fn key_bindings(&self) -> KeyBindings {
        (&**self).key_bindings()
    }

}

impl<T, F> fmt::Write for Context<T, F> {
    fn write_str(&mut self, s: &str) -> fmt::Result {
        self.buffer.push_str(s);

        Ok(())
    }
}

impl<T: Tty, F: Fn(&Buffer) -> Vec<(usize, usize)>> EditorContext for Context<T, F> {
    type Terminal = T;
    type WordDividerIter = <Vec<(usize, usize)> as IntoIterator>::IntoIter;

    fn history(&self) -> &History {
        &self.history
    }

    fn history_mut(&mut self) -> &mut History {
        &mut self.history
    }

    fn word_divider(&self, buf: &Buffer) -> Self::WordDividerIter {
        (self.word_divider_fn)(buf).into_iter()
    }

    fn terminal(&self) -> &Self::Terminal {
        &self.terminal
    }

    fn terminal_mut(&mut self) -> &mut Self::Terminal {
        &mut self.terminal
    }

    fn key_bindings(&self) -> KeyBindings {
        self.key_bindings
    }

}

impl<T: Default> Default for Context<T> {
    fn default() -> Self {
        Self::with_terminal(T::default())
    }
}

impl Context {
    pub fn new() -> Self {
        Self::default()
    }
}

impl<T> Context<T> {
    pub fn with_terminal(terminal: T) -> Self {
        Context {
            history: History::new(),
            word_divider_fn: Box::new(get_buffer_words),
            key_bindings: KeyBindings::Emacs,
            buffer: String::with_capacity(512),
            terminal,
        }
    }
}

#[cfg(test)]
impl Context<crate::test::TestTty> {
    pub(crate) fn test() -> Self {
        Self::default()
    }
}

impl<T> From<T> for Context<T> {
    fn from(value: T) -> Self {
        Self::with_terminal(value)
    }
}
