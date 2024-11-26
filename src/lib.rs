// MIT License

// Copyright (c) 2016 Jerome Froelich

// Permission is hereby granted, free of charge, to any person obtaining a copy
// of this software and associated documentation files (the "Software"), to deal
// in the Software without restriction, including without limitation the rights
// to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
// copies of the Software, and to permit persons to whom the Software is
// furnished to do so, subject to the following conditions:

// The above copyright notice and this permission notice shall be included in all
// copies or substantial portions of the Software.

// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
// IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
// FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
// AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
// LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
// OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
// SOFTWARE.

//! A minimal implementation of consistent hashing as described in [Consistent
//! Hashing and Random Trees: Distributed Caching Protocols for Relieving Hot
//! Spots on the World Wide Web](https://www.akamai.com/es/es/multimedia/documents/technical-publication/consistent-hashing-and-random-trees-distributed-caching-protocols-for-relieving-hot-spots-on-the-world-wide-web-technical-publication.pdf).
//! Clients can use the `HashRing` struct to add consistent hashing to their
//! applications. `HashRing`'s API consists of three methods: `add`, `remove`,
//! and `get` for adding a node to the ring, removing a node from the ring, and
//! getting the node responsible for the provided key.
//!
//! ## Example
//!
//! Below is a simple example of how an application might use `HashRing` to make
//! use of consistent hashing. Since `HashRing` exposes only a minimal API clients
//! can build other abstractions, such as virtual nodes, on top of it. The example
//! below shows one potential implementation of virtual nodes on top of `HashRing`
//!
//! ``` rust,no_run
//! extern crate hashring;
//!
//! use std::net::{IpAddr, SocketAddr};
//! use std::str::FromStr;
//!
//! use hashring::HashRing;
//!
//! #[derive(Debug, Copy, Clone, Hash, PartialEq)]
//! struct VNode {
//!     id: usize,
//!     addr: SocketAddr,
//! }
//!
//! impl VNode {
//!     fn new(ip: &str, port: u16, id: usize) -> Self {
//!         let addr = SocketAddr::new(IpAddr::from_str(&ip).unwrap(), port);
//!         VNode {
//!             id: id,
//!             addr: addr,
//!         }
//!     }
//! }
//!
//! fn main() {
//!     let mut ring: HashRing<VNode> = HashRing::new();
//!
//!     let mut nodes = vec![];
//!     nodes.push(VNode::new("127.0.0.1", 1024, 1));
//!     nodes.push(VNode::new("127.0.0.1", 1024, 2));
//!     nodes.push(VNode::new("127.0.0.2", 1024, 1));
//!     nodes.push(VNode::new("127.0.0.2", 1024, 2));
//!     nodes.push(VNode::new("127.0.0.2", 1024, 3));
//!     nodes.push(VNode::new("127.0.0.3", 1024, 1));
//!
//!     for node in nodes {
//!         ring.add(node);
//!     }
//!
//!     println!("{:?}", ring.get(&"foo"));
//!     println!("{:?}", ring.get(&"bar"));
//!     println!("{:?}", ring.get(&"baz"));
//! }
//! ```

extern crate siphasher;

use siphasher::sip::SipHasher;
use std::cmp::Ordering;
use std::fmt::Debug;
use std::hash::BuildHasher;
use std::hash::Hash;

#[derive(Clone, PartialEq, Debug)]
pub struct DefaultHashBuilder;

impl BuildHasher for DefaultHashBuilder {
    type Hasher = SipHasher;

    fn build_hasher(&self) -> Self::Hasher {
        SipHasher::new()
    }
}

// Node is an internal struct used to encapsulate the nodes that will be added and
// removed from `HashRing`
#[derive(Clone, Debug)]
pub struct Node<T, M> {
    key: u64,
    pub node: T,
    pub meta: Option<M>,
}

impl<T, M> Node<T, M> {
    fn new(key: u64, node: T) -> Node<T, M> {
        Node {
            key,
            node,
            meta: None,
        }
    }

    fn new_with_meta(key: u64, node: T, meta: Option<M>) -> Node<T, M> {
        Node { key, node, meta }
    }

    pub fn replace_meta(&mut self, meta: M) {
        self.meta.replace(meta);
    }

    pub fn take_meta(&mut self) -> Option<M> {
        self.meta.take()
    }
}

// Implement `PartialEq`, `Eq`, `PartialOrd` and `Ord` so we can sort `Node`s
impl<T, M> PartialEq for Node<T, M> {
    fn eq(&self, other: &Node<T, M>) -> bool {
        self.key == other.key
    }
}

impl<T, M> Eq for Node<T, M> {}

impl<T, M> PartialOrd for Node<T, M> {
    fn partial_cmp(&self, other: &Node<T, M>) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<T, M> Ord for Node<T, M> {
    fn cmp(&self, other: &Node<T, M>) -> Ordering {
        self.key.cmp(&other.key)
    }
}

#[derive(Clone, PartialEq, Debug)]
pub struct HashRing<T, M = (), S = DefaultHashBuilder> {
    hash_builder: S,
    ring: Vec<Node<T, M>>,
}

impl<T, M> Default for HashRing<T, M> {
    fn default() -> Self {
        HashRing {
            hash_builder: DefaultHashBuilder,
            ring: Vec::new(),
        }
    }
}

/// Hash Ring
///
/// A hash ring that provides consistent hashing for nodes that are added to it.
impl<T, M> HashRing<T, M> {
    /// Create a new `HashRing`.
    pub fn new() -> HashRing<T, M> {
        Default::default()
    }
}

impl<T, M, S> HashRing<T, M, S> {
    /// Creates an empty `HashRing` which will use the given hash builder.
    pub fn with_hasher(hash_builder: S) -> HashRing<T, M, S> {
        HashRing {
            hash_builder,
            ring: Vec::new(),
        }
    }

    /// Get the number of nodes in the hash ring.
    pub fn len(&self) -> usize {
        self.ring.len()
    }

    /// Returns true if the ring has no elements.
    pub fn is_empty(&self) -> bool {
        self.ring.len() == 0
    }
}

impl<T: Hash, M, S: BuildHasher> HashRing<T, M, S> {
    /// Add `node` to the hash ring.
    pub fn add(&mut self, node: T) {
        self.add_with_meta(node, None);
    }

    /// Add `node`, with `meta` option, to the hash ring.
    pub fn add_with_meta(&mut self, node: T, meta: Option<M>) {
        let key = get_key(&self.hash_builder, &node);
        self.ring.push(Node::new_with_meta(key, node, meta));
        self.ring.sort();
    }

    pub fn batch_add(&mut self, nodes: Vec<T>) {
        for node in nodes {
            let key = get_key(&self.hash_builder, &node);
            self.ring.push(Node::new(key, node));
        }
        self.ring.sort()
    }

    /// Remove `node` from the hash ring. Returns an `Option` that will contain the `node`
    /// if it was in the hash ring or `None` if it was not present.
    pub fn remove(&mut self, node: &T) -> Option<T> {
        let key = get_key(&self.hash_builder, node);
        match self.ring.binary_search_by(|node| node.key.cmp(&key)) {
            Err(_) => None,
            Ok(n) => Some(self.ring.remove(n).node),
        }
    }

    /// Get the node responsible for `key`. Returns an `Option` that will contain the `node`
    /// if the hash ring is not empty or `None` if it was empty.
    pub fn get_node<U: Hash>(&self, key: &U) -> Option<&Node<T, M>> {
        if self.ring.is_empty() {
            return None;
        }

        let k = get_key(&self.hash_builder, key);
        let n = match self.ring.binary_search_by(|node| node.key.cmp(&k)) {
            Err(n) => n,
            Ok(n) => n,
        };

        let node = if n == self.ring.len() {
            &self.ring[0]
        } else {
            &self.ring[n]
        };

        Some(node)
    }

    /// Get a mutable reference to the node responsible for `key`. Returns an `Option` that will contain the `node`
    /// if the hash ring is not empty or `None` if it was empty.
    ///
    /// Useful for modifying the node's `meta`.
    pub fn get_node_mut<U: Hash>(&mut self, key: &U) -> Option<&mut Node<T, M>> {
        if self.ring.is_empty() {
            return None;
        }

        let k = get_key(&self.hash_builder, key);
        let n = match self.ring.binary_search_by(|node| node.key.cmp(&k)) {
            Err(n) => n,
            Ok(n) => n,
        };

        let node = if n == self.ring.len() {
            &mut self.ring[0]
        } else {
            &mut self.ring[n]
        };

        Some(node)
    }

    /// Get the node responsible for `key`. Returns an `Option` that will contain the `node`
    /// if the hash ring is not empty or `None` if it was empty.
    pub fn get<U: Hash>(&self, key: &U) -> Option<&T> {
        self.get_node(key).map(|node| &node.node)
    }

    /// Get the node responsible for `key` along with the next `replica` nodes after.
    /// Returns None when the ring is empty. If `replicas` is larger than the length
    /// of the ring, this function will shrink to just contain the entire ring.
    pub fn get_with_replicas<U: Hash>(&self, key: &U, replicas: usize) -> Option<Vec<T>>
    where
        T: Clone + Debug,
        M: Clone,
    {
        if self.ring.is_empty() {
            return None;
        }

        let replicas = if replicas > self.ring.len() {
            self.ring.len()
        } else {
            replicas + 1
        };

        let k = get_key(&self.hash_builder, key);
        let n = match self.ring.binary_search_by(|node| node.key.cmp(&k)) {
            Err(n) => n,
            Ok(n) => n,
        };

        let mut nodes = self.ring.clone();
        nodes.rotate_left(n);

        let replica_nodes = nodes
            .iter()
            .cycle()
            .take(replicas)
            .map(|node| node.node.clone())
            .collect();

        Some(replica_nodes)
    }
}

pub struct HashRingIterator<T, M> {
    ring: std::vec::IntoIter<Node<T, M>>,
}

impl<T, M> Iterator for HashRingIterator<T, M> {
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        self.ring.next().map(|node| node.node)
    }
}

impl<T, M> IntoIterator for HashRing<T, M> {
    type Item = T;

    type IntoIter = HashRingIterator<T, M>;

    fn into_iter(self) -> Self::IntoIter {
        HashRingIterator {
            ring: self.ring.into_iter(),
        }
    }
}

// An internal function for converting a reference to a hashable type into a `u64` which
// can be used as a key in the hash ring.
fn get_key<S, T>(hash_builder: &S, input: T) -> u64
where
    S: BuildHasher,
    T: Hash,
{
    hash_builder.hash_one(input)
}

#[cfg(test)]
mod tests {
    use std::hash::Hash;
    use std::hash::Hasher;
    use std::net::{Ipv4Addr, SocketAddrV4};
    use std::str::FromStr;

    use super::HashRing;

    #[derive(Debug, Copy, Clone, PartialEq)]
    struct VNode {
        id: usize,
        addr: SocketAddrV4,
    }

    impl VNode {
        fn new(ip: &str, port: u16, id: usize) -> Self {
            let addr = SocketAddrV4::new(Ipv4Addr::from_str(ip).unwrap(), port);
            VNode { id, addr }
        }
    }

    impl Hash for VNode {
        fn hash<H: Hasher>(&self, s: &mut H) {
            (self.id, self.addr.port(), self.addr.ip()).hash(s)
        }
    }

    #[test]
    fn add_and_remove_nodes() {
        let mut ring: HashRing<VNode> = HashRing::new();

        assert_eq!(ring.len(), 0);
        assert!(ring.is_empty());

        let vnode1 = VNode::new("127.0.0.1", 1024, 1);
        let vnode2 = VNode::new("127.0.0.1", 1024, 2);
        let vnode3 = VNode::new("127.0.0.2", 1024, 1);

        ring.add(vnode1);
        ring.add(vnode2);
        ring.add(vnode3);
        assert_eq!(ring.len(), 3);
        assert!(!ring.is_empty());

        assert_eq!(ring.remove(&vnode2).unwrap(), vnode2);
        assert_eq!(ring.len(), 2);

        let vnode4 = VNode::new("127.0.0.2", 1024, 2);
        let vnode5 = VNode::new("127.0.0.2", 1024, 3);
        let vnode6 = VNode::new("127.0.0.3", 1024, 1);

        ring.batch_add(vec![vnode4, vnode5, vnode6]);

        assert_eq!(ring.remove(&vnode1).unwrap(), vnode1);
        assert_eq!(ring.remove(&vnode3).unwrap(), vnode3);
        assert_eq!(ring.remove(&vnode6).unwrap(), vnode6);
        assert_eq!(ring.len(), 2);
    }

    #[test]
    fn get_nodes() {
        let mut ring: HashRing<VNode> = HashRing::new();

        assert_eq!(ring.get(&"foo"), None);

        let vnode1 = VNode::new("127.0.0.1", 1024, 1);
        let vnode2 = VNode::new("127.0.0.1", 1024, 2);
        let vnode3 = VNode::new("127.0.0.2", 1024, 1);
        let vnode4 = VNode::new("127.0.0.2", 1024, 2);
        let vnode5 = VNode::new("127.0.0.2", 1024, 3);
        let vnode6 = VNode::new("127.0.0.3", 1024, 1);

        ring.add(vnode1);
        ring.add(vnode2);
        ring.add(vnode3);
        ring.add(vnode4);
        ring.add(vnode5);
        ring.add(vnode6);

        assert_eq!(ring.get(&"foo"), Some(&vnode6));
        assert_eq!(ring.get(&"bar"), Some(&vnode5));
        assert_eq!(ring.get(&"baz"), Some(&vnode4));

        assert_eq!(ring.get(&"abc"), Some(&vnode1));
        assert_eq!(ring.get(&"def"), Some(&vnode1));
        assert_eq!(ring.get(&"ghi"), Some(&vnode6));

        assert_eq!(ring.get(&"cat"), Some(&vnode5));
        assert_eq!(ring.get(&"dog"), Some(&vnode4));
        assert_eq!(ring.get(&"bird"), Some(&vnode4));

        // at least each node as a key
        let mut nodes = vec![0; 6];
        for x in 0..50_000 {
            let node = ring.get(&x).unwrap();
            if vnode1 == *node {
                nodes[0] += 1;
            }
            if vnode2 == *node {
                nodes[1] += 1;
            }
            if vnode3 == *node {
                nodes[2] += 1;
            }
            if vnode4 == *node {
                nodes[3] += 1;
            }
            if vnode5 == *node {
                nodes[4] += 1;
            }
            if vnode6 == *node {
                nodes[5] += 1;
            }
        }
        println!("{:?}", nodes);
        assert!(nodes.iter().all(|x| *x != 0));
    }

    #[test]
    fn get_nodes_with_replicas() {
        let mut ring: HashRing<VNode> = HashRing::new();

        assert_eq!(ring.get(&"foo"), None);
        assert_eq!(ring.get_with_replicas(&"foo", 1), None);

        let vnode1 = VNode::new("127.0.0.1", 1024, 1);
        let vnode2 = VNode::new("127.0.0.1", 1024, 2);
        let vnode3 = VNode::new("127.0.0.2", 1024, 3);
        let vnode4 = VNode::new("127.0.0.2", 1024, 4);
        let vnode5 = VNode::new("127.0.0.2", 1024, 5);
        let vnode6 = VNode::new("127.0.0.3", 1024, 6);

        ring.add(vnode1);
        ring.add(vnode2);
        ring.add(vnode3);
        ring.add(vnode4);
        ring.add(vnode5);
        ring.add(vnode6);

        assert_eq!(
            ring.get_with_replicas(&"bar", 2).unwrap(),
            vec![vnode3, vnode1, vnode2]
        );

        assert_eq!(
            ring.get_with_replicas(&"foo", 4).unwrap(),
            vec![vnode5, vnode4, vnode3, vnode1, vnode2]
        );
    }

    #[test]
    fn get_with_replicas_returns_too_many_replicas() {
        let mut ring: HashRing<VNode> = HashRing::new();

        assert_eq!(ring.get(&"foo"), None);
        assert_eq!(ring.get_with_replicas(&"foo", 1), None);

        let vnode1 = VNode::new("127.0.0.1", 1024, 1);
        let vnode2 = VNode::new("127.0.0.1", 1024, 2);
        let vnode3 = VNode::new("127.0.0.2", 1024, 3);
        let vnode4 = VNode::new("127.0.0.2", 1024, 4);
        let vnode5 = VNode::new("127.0.0.2", 1024, 5);
        let vnode6 = VNode::new("127.0.0.3", 1024, 6);

        ring.add(vnode1);
        ring.add(vnode2);
        ring.add(vnode3);
        ring.add(vnode4);
        ring.add(vnode5);
        ring.add(vnode6);

        assert_eq!(
            ring.get_with_replicas(&"bar", 20).unwrap(),
            vec![vnode3, vnode1, vnode2, vnode6, vnode5, vnode4],
            "too high of replicas causes the count to shrink to ring length"
        );
    }

    #[test]
    fn into_iter() {
        let mut ring: HashRing<VNode> = HashRing::new();

        assert_eq!(ring.get(&"foo"), None);

        let vnode1 = VNode::new("127.0.0.1", 1024, 1);
        let vnode2 = VNode::new("127.0.0.1", 1024, 2);
        let vnode3 = VNode::new("127.0.0.2", 1024, 1);

        ring.add(vnode1);
        ring.add(vnode2);
        ring.add(vnode3);

        let mut iter = ring.into_iter();

        assert_eq!(Some(vnode3), iter.next());
        assert_eq!(Some(vnode1), iter.next());
        assert_eq!(Some(vnode2), iter.next());
        assert_eq!(None, iter.next());
    }

    #[test]
    fn hash_ring_eq() {
        let mut ring: HashRing<VNode> = HashRing::new();
        let mut other = ring.clone();
        assert_eq!(ring, other);
        assert_eq!(ring.len(), 0);

        let vnode1 = VNode::new("127.0.0.1", 1024, 1);
        let vnode2 = VNode::new("127.0.0.1", 1024, 2);
        let vnode3 = VNode::new("127.0.0.2", 1024, 1);
        other.add(vnode1);
        other.add(vnode2);
        other.add(vnode3);
        assert_ne!(ring, other);
        assert_eq!(other.len(), 3);

        other.remove(&vnode1).unwrap();
        other.remove(&vnode2).unwrap();
        other.remove(&vnode3).unwrap();
        assert_eq!(ring, other);
        assert_eq!(other.len(), 0);

        ring.add(vnode1);
        ring.add(vnode2);
        other.add(vnode2);
        other.add(vnode3);
        other.remove(&vnode3);
        ring.remove(&vnode1);
        assert_eq!(ring, other);
        assert_eq!(ring.len(), 1);
        assert_eq!(other.len(), 1);
    }
}
