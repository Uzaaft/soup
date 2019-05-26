use html5ever::rcdom::{self, Handle, NodeData};
use std::{fmt, marker::PhantomData, rc::Rc};

use crate::pattern::Pattern;
use crate::attribute;

/// Represents the act of matching a node in the html tree
pub trait Query {
    fn matches(&self, node: &rcdom::Node) -> bool;
}

impl Query for () {
    fn matches(&self, _: &rcdom::Node) -> bool {
        true
    }
}

/// This type implements the "compile-time onion" mechanism for building up a dynamic number
/// of queries. It looks kinda like a linked list, but importantly, it also implements `Query`,
/// so it can hold another QueryWrapper. When the user adds more than one query to the chain,
/// a new QueryWrapper wraps the old one, and replaces it at the top-level.
pub struct QueryWrapper<'a, T: Query, U: Query> {
    inner: T,
    next: Option<U>,
    _l: PhantomData<&'a ()>,
}

impl<'a, T, U> Query for QueryWrapper<'a, T, U>
where
    T: Query + 'a,
    U: Query + 'a,
{
    /// This is where the QueryWrapper recursively "unwraps" itself
    fn matches(&self, node: &rcdom::Node) -> bool {
        let inner_match = self.inner.matches(node);
        if let Some(ref next) = self.next {
            let next_match = next.matches(node);
            next_match && inner_match
        } else {
            inner_match
        }
    }
}

impl<'a, T, U, V> QueryWrapper<'a, T, QueryWrapper<'a, U, V>>
where
    T: Query + 'a,
    U: Query + 'a,
    V: Query + 'a,
{
    /// This is where the "wrapping" operation happens. ren
    fn wrap(
        inner: T,
        query: QueryWrapper<'a, U, V>,
    ) -> QueryWrapper<'a, T, QueryWrapper<'a, U, V>> {
        QueryWrapper {
            inner,
            next: Some(query),
            _l: PhantomData,
        }
    }
}

impl<'a, T, U> fmt::Debug for QueryWrapper<'a, T, U>
where
    T: Query + fmt::Debug,
    U: Query + fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("QueryWrapper")
            .field("inner", &self.inner)
            .field("next", &self.next)
            .finish()
    }
}

pub(crate) type EmptyQueryWrapper<'a> = QueryWrapper<'a, (), ()>;

// base case for the QueryWrapper
impl<'a> EmptyQueryWrapper<'a> {
    fn new() -> EmptyQueryWrapper<'a> {
        let none: Option<()> = None;
        QueryWrapper {
            inner: (),
            next: none,
            _l: PhantomData,
        }
    }
}


/// Construct a query to apply to an HTML tree
///
/// # Example
///
/// ```rust
/// # extern crate soup;
/// # use soup::prelude::*;
/// # use std::error::Error;
/// # fn main() -> Result<(), Box<Error>> {
/// let soup = Soup::new(r#"<div id="foo">BAR</div><div id="baz">QUUX</div>"#);
/// let query = soup.tag("div")         // result must be a div
///                 .attr("id", "foo")  // with id "foo"
///                 .find();            // executes the query, returns the first result
/// #   Ok(())
/// # }
pub struct QueryBuilder<'a, T: Query + 'a = (), U: Query + 'a = ()> {
    handle: Handle,
    queries: QueryWrapper<'a, T, U>,
    limit: Option<usize>,
    recursive: bool,
}

impl<'a, T: Query + 'a, U: Query + 'a> fmt::Debug for QueryBuilder<'a, T, U> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "QueryBuilder(«Handle», «Queries»)")
    }
}

impl<'a> QueryBuilder<'a, (), ()> {
    pub(crate) fn new(handle: Handle) -> QueryBuilder<'a, (), ()> {
        QueryBuilder {
            handle,
            queries: QueryWrapper::new(),
            limit: None,
            recursive: true,
        }
    }
}

impl<'a, T, U> QueryBuilder<'a, T, U>
where
    T: Query + 'a,
    U: Query + 'a,
{
    /// Adds a limit to the number of results that can be returned
    ///
    /// This method adds an upper bound to the number of results that will be
    /// returned by the query
    ///
    /// # Example
    ///
    /// ```rust
    /// # extern crate soup;
    /// # use std::error::Error;
    /// # use soup::prelude::*;
    /// # fn main() -> Result<(), Box<Error>> {
    /// let soup = Soup::new(r#"<div id="one"></div><div id="two"></div><div id="three></div>"#);
    /// let results = soup.tag("div").limit(2).find_all().collect::<Vec<_>>();
    /// assert_eq!(results.len(), 2);
    /// #   Ok(())
    /// # }
    /// ```
    pub fn limit(mut self, limit: usize) -> QueryBuilder<'a, T, U> {
        self.limit = Some(limit);
        self
    }

    fn push_query<Q: Query + 'a>(self, query: Q) -> QueryBuilder<'a, Q, QueryWrapper<'a, T, U>> {
        let queries = QueryWrapper::<'a, Q, QueryWrapper<'a, T, U>>::wrap(query, self.queries);
        QueryBuilder {
            handle: self.handle,
            queries,
            limit: self.limit,
            recursive: self.recursive,
        }
    }

    /// Specifies a tag for which to search
    ///
    /// # Example
    ///
    /// ```rust
    /// # extern crate soup;
    /// # use std::error::Error;
    /// # use soup::prelude::*;
    /// # fn main() -> Result<(), Box<Error>> {
    /// let soup =
    ///     Soup::new(r#"<div>Test</div><section><b id="bold-tag">SOME BOLD TEXT</b></section>"#);
    /// let result = soup.tag("b").find().unwrap();
    /// assert_eq!(result.get("id"), Some("bold-tag".to_string()));
    /// #   Ok(())
    /// # }
    /// ```
    pub fn tag<P: Pattern>(self, tag: P) -> QueryBuilder<'a, TagQuery<P>, QueryWrapper<'a, T, U>> {
        self.push_query(TagQuery::new(tag))
    }

    /// Specifies a string to search for in a text node
    ///
    /// # Example
    ///
    /// ```rust
    /// # extern crate soup;
    /// # extern crate regex;
    /// # use std::error::Error;
    /// # use regex::Regex;
    /// # use soup::prelude::*;
    /// # fn main() -> Result<(), Box<Error>> {
    /// let soup = Soup::new(r#"<div>Test</div><b id="bold-tag">SOME BOLD TEXT</b></div>"#);
    /// let result = soup.string(Regex::new(r#".*BOLD.*"#).expect("Couldn't create regex")).find().expect("Couldn't find tag with text 'BOLD'");
    /// assert_eq!(result.get("id"), Some("bold-tag".to_string()));
    /// #   Ok(())
    /// # }
    /// ```
    pub fn string<P: Pattern>(self, string: P) -> QueryBuilder<'a, TextQuery<P>, QueryWrapper<'a, T, U>> {
        self.push_query(TextQuery::new(string))
    }

    /// Searches for a tag that has an attribute with the specified name
    ///
    /// # Example
    ///
    /// ```rust
    /// # extern crate soup;
    /// # use std::error::Error;
    /// # use soup::prelude::*;
    /// # fn main() -> Result<(), Box<Error>> {
    /// let soup = Soup::new(r#"<div>Test</div><section><b id="bold-tag">SOME BOLD TEXT</b></section>"#);
    /// let result = soup.attr_name("id").find().unwrap();
    /// assert_eq!(result.name(), "b");
    /// #   Ok(())
    /// # }
    /// ```
    pub fn attr_name<P>(self, name: P) -> QueryBuilder<'a, AttrQuery<P, bool>, QueryWrapper<'a, T, U>>
    where
        P: Pattern
    {
        self.push_query(AttrQuery::new(name, true))
    }

    /// Search for a node with any attribute with a value that matches the specified value
    ///
    /// # Example
    ///
    /// ```rust
    /// # extern crate soup;
    /// # use std::error::Error;
    /// # use soup::prelude::*;
    /// # fn main() -> Result<(), Box<Error>> {
    /// let soup = Soup::new(r#"<div>Test</div><section><b id="bold-tag">SOME BOLD TEXT</b></section>"#);
    /// let result = soup.attr_value("bold-tag").find().unwrap();
    /// assert_eq!(result.name(), "b");
    /// #   Ok(())
    /// # }
    /// ```
    pub fn attr_value<P>(self, value: P) -> QueryBuilder<'a, AttrQuery<bool, P>, QueryWrapper<'a, T, U>>
    where
        P: Pattern
    {
        self.push_query(AttrQuery::new(true, value))
    }

    /// Specifies an attribute name/value pair for which to search
    ///
    /// # Example
    ///
    /// ```rust
    /// # extern crate soup;
    /// # use std::error::Error;
    /// # use soup::prelude::*;
    /// # fn main() -> Result<(), Box<Error>> {
    /// let soup =
    ///     Soup::new(r#"<div>Test</div><section><b id="bold-tag">SOME BOLD TEXT</b></section>"#);
    /// let result = soup.attr("id", "bold-tag").find().unwrap();
    /// assert_eq!(result.name(), "b".to_string());
    /// #   Ok(())
    /// # }
    /// ```
    pub fn attr<P, Q>(
        self,
        name: P,
        value: Q,
    ) -> QueryBuilder<'a, AttrQuery<P, Q>, QueryWrapper<'a, T, U>>
    where
        P: Pattern,
        Q: Pattern,
    {
        self.push_query(AttrQuery::new(name, value))
    }

    /// Specifies a class name for which to search
    ///
    /// # Example
    ///
    /// ```rust
    /// # extern crate soup;
    /// # use std::error::Error;
    /// # use soup::prelude::*;
    /// # fn main() -> Result<(), Box<Error>> {
    /// let soup = Soup::new(
    ///     r#"<div>Test</div><section class="content"><b id="bold-tag">SOME BOLD TEXT</b></section>"#,
    /// );
    /// let result = soup.class("content").find().unwrap();
    /// assert_eq!(result.name(), "section".to_string());
    /// #   Ok(())
    /// # }
    /// ```
    pub fn class<P: Pattern>(
        self,
        value: P,
    ) -> QueryBuilder<'a, AttrQuery<&'static str, P>, QueryWrapper<'a, T, U>> {
        self.attr("class", value)
    }

    /// Specifies whether the query should recurse all the way through the document, or
    /// stay localized to the queried tag and it's children
    pub fn recursive(mut self, recursive: bool) -> Self {
        self.recursive = recursive;
        self
    }

    /// Executes the query, and returns either the first result, or `None`
    ///
    /// # Example
    ///
    /// ```rust
    /// # extern crate soup;
    /// # use std::error::Error;
    /// # use soup::prelude::*;
    /// # fn main() -> Result<(), Box<Error>> {
    /// let soup = Soup::new(
    ///     r#"<ul><li id="one">One</li><li id="two">Two</li><li id="three">Three</li></ul>"#,
    /// );
    /// let result = soup.tag("li").find().unwrap();
    /// assert_eq!(result.get("id"), Some("one".to_string()));
    /// #   Ok(())
    /// # }
    /// ```
    pub fn find(mut self) -> Option<Handle> {
        self.limit = Some(1);
        self.into_iter().nth(0)
    }

    /// Executes the query, and returns an iterator of the results
    ///
    /// # Example
    ///
    /// ```rust
    /// # extern crate soup;
    /// # use std::error::Error;
    /// # use soup::prelude::*;
    /// # fn main() -> Result<(), Box<Error>> {
    /// let soup = Soup::new(
    ///     r#"<ul><li id="one">One</li><li id="two">Two</li><li id="three">Three</li></ul>"#,
    /// );
    /// let results = soup.tag("li").find_all().collect::<Vec<_>>();
    /// assert_eq!(results.len(), 3);
    /// assert_eq!(results[0].display(), "<li id=\"one\">One</li>");
    /// assert_eq!(results[1].display(), "<li id=\"two\">Two</li>");
    /// assert_eq!(results[2].display(), "<li id=\"three\">Three</li>");
    /// #   Ok(())
    /// # }
    /// ```
    pub fn find_all(self) -> BoxNodeIter<'a> {
        self.into_iter()
    }
}

struct NodeIterator<'a, T: Query + 'a, U: Query + 'a> {
    handle: Handle,
    queries: Rc<QueryWrapper<'a, T, U>>,
    done: bool,
}

impl<'a, T: Query + 'a, U: Query + 'a> NodeIterator<'a, T, U> {
    fn new(handle: Handle, queries: Rc<QueryWrapper<'a, T, U>>) -> NodeIterator<'a, T, U> {
        NodeIterator {
            handle,
            queries,
            done: false,
        }
    }
}

impl<'a, T, U> Iterator for NodeIterator<'a, T, U>
where
    T: Query + 'a,
    U: Query + 'a,
{
    type Item = Option<Handle>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.done {
            return None;
        }
        if Query::matches(&*self.queries, &self.handle) {
            self.done = true;
            Some(Some(self.handle.clone()))
        } else {
            self.done = true;
            Some(None)
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (0, Some(1))
    }
}

type BoxOptionNodeIter<'a> = Box<dyn Iterator<Item = Option<Handle>> + 'a>;
type BoxNodeIter<'a> = Box<dyn Iterator<Item = Handle> + 'a>;

impl<'a, T: Query + 'a, U: Query + 'a> IntoIterator for QueryBuilder<'a, T, U> {
    type IntoIter = BoxNodeIter<'a>;
    type Item = Handle;

    fn into_iter(self) -> Self::IntoIter {
        let queries = Rc::new(self.queries);
        let recurse_levels = if self.recursive {
            None
        } else {
            Some(1u8)
        };
        let iter = build_iter(self.handle, queries, recurse_levels);
        let iter: BoxNodeIter<'_> = Box::new(iter.flat_map(|node| node));
        if let Some(limit) = self.limit {
            let iter: BoxNodeIter<'_> = Box::new(iter.take(limit));
            iter
        } else {
            iter
        }
    }
}

fn build_iter<'a, T: Query + 'a, U: Query + 'a>(
    handle: Handle,
    queries: Rc<QueryWrapper<'a, T, U>>,
    levels: Option<u8>,
) -> BoxOptionNodeIter<'a> {
    let iter = NodeIterator::new(handle.clone(), queries.clone());
    let iter: BoxOptionNodeIter<'_> = Box::new(iter);
    if let Some(l) = levels {
        if l == 0 {
            return iter;
        }
    }
    handle.children.borrow().iter().fold(iter, |acc, child| {
        let child_iter = build_iter(child.clone(), queries.clone(), levels.map(|l| l - 1));
        let child_iter: BoxOptionNodeIter<'_> = Box::new(child_iter);
        Box::new(acc.chain(child_iter))
    })
}

/*** Types of Queries ***/

pub struct TextQuery<P> {
    inner: P,
}

impl<P: Pattern> TextQuery<P> {
    fn new(inner: P) -> TextQuery<P> {
        TextQuery {
            inner,
        }
    }
}

impl<P> fmt::Debug for TextQuery<P>
where
    P: Pattern + fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("TextQuery")
            .field("inner", &self.inner)
            .finish()
    }
}

impl<P: Pattern> Query for TextQuery<P> {
    fn matches(&self, node: &rcdom::Node) -> bool {
        match node.data {
            NodeData::Element {
                ..
            } => {
                // it would be easier to just have this be
                //
                // node.children.borrow().iter().any(|n| self.matches(n))
                //
                // but then this would recurse down the whole tree
                for n in node.children.borrow().iter() {
                    let data = &n.data;
                    if let NodeData::Text { ref contents, .. } = data {
                        let c = contents.borrow().to_string();
                        if self.inner.matches(&c) {
                            return true;
                        }
                    }
                }
                false
            },
            NodeData::Text {
                ref contents, ..
            } => {
                let c = contents.borrow().to_string();
                self.inner.matches(&c)
            },
            _ => false,
        }
    }
}

pub struct TagQuery<P> {
    inner: P,
}

impl<P: Pattern> TagQuery<P> {
    fn new(inner: P) -> TagQuery<P> {
        TagQuery {
            inner,
        }
    }
}

impl<P> fmt::Debug for TagQuery<P>
where
    P: Pattern + fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("TagQuery")
            .field("inner", &self.inner)
            .finish()
    }
}

impl<P: Pattern> Query for TagQuery<P> {
    fn matches(&self, node: &rcdom::Node) -> bool {
        match node.data {
            NodeData::Element {
                ref name, ..
            } => self.inner.matches(name.local.as_ref()),
            _ => false,
        }
    }
}

pub struct AttrQuery<K, V> {
    key: K,
    value: V,
}

impl<K, V> AttrQuery<K, V>
where
    K: Pattern,
    V: Pattern,
{
    fn new(key: K, value: V) -> AttrQuery<K, V> {
        AttrQuery {
            key,
            value,
        }
    }
}

impl<K, V> fmt::Debug for AttrQuery<K, V>
where
    K: Pattern + fmt::Debug,
    V: Pattern + fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("AttrQuery")
            .field("key", &self.key)
            .field("value", &self.value)
            .finish()
    }
}

impl<K, V> Query for AttrQuery<K, V>
where
    K: Pattern,
    V: Pattern,
{
    fn matches(&self, node: &rcdom::Node) -> bool {
        attribute::list_aware_match(&node, &self.key, &self.value)
    }
}

