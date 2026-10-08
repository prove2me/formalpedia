-- Prove2me | Theorems.Thm_TuranMatching_ColorCritical_proposition_3_1
-- name    : TuranMatching.ColorCritical.proposition_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T03:33:22.779989+00:00
-- url     : https://prove2.me/theorems/fa96b555-539f-4731-a234-0984064639c4
-- title:
--   Proposition 3.1 — for color-critical H with χ(H)=k+1>2, s > s₀(H) and n > n₀(s), the maximum edges of an H-free graph with ν ≤ s is g(n,k,s)
-- statement:
--   For a finite graph $H$, a graph $G$ is $H$-free if it contains no subgraph isomorphic to $H$. Let $\nu(G)$ be the matching number of $G$, and let $g(n,k,s)$ be the number of edges of the complete $k$-partite graph $G(n,k,s)$ on $n$ vertices with $k-1$ classes of sizes as equal as possible and total size $s$, plus one class of size $n-s$.
--
--   **Proposition 3.1.** There is a function $n_0:\mathbb N\to\mathbb N$ with the following property. For every fixed color-critical graph $H$ of chromatic number $k+1>2$ there is $s_0(H)$ such that for any $s>s_0(H)$ and any $n>n_0(s)$,
--   $$\max\{\,|E(G)| : G \text{ an } H\text{-free graph on } n \text{ vertices with } \nu(G)\le s\,\}=g(n,k,s).$$
--   That is, every $H$-free graph on $n$ vertices with matching number at most $s$ has at most $g(n,k,s)$ edges, and some $H$-free graph on $n$ vertices with matching number at most $s$ has exactly $g(n,k,s)$ edges.
--
--   The result is a Turán-type theorem under a matching constraint: for $H=K_{k+1}$ it recovers the large-$n$ case of the authors' Theorem 1.1, and it extends it to every color-critical forbidden graph once $s$ is large in terms of $H$.
--
--   **Formalization Note** The order of quantifiers is the page's: $s_0$ depends on $H$ only and $n_0$ is a function of $s$ alone, chosen before $H$ (the page writes $n_0(s)$). The maximum is stated as an upper bound together with an attaining graph. $\chi(H)=k+1$ is an equality in $\mathbb N\cup\{\infty\}$, and $k+1>2$ is the page's hypothesis. $H$-freeness is non-induced subgraph containment (Mathlib's `SimpleGraph.Free`); the vertex type of $H$ is any finite type in the lowest universe. Vertices of $G$ are `Fin n`.
-- source:
--   Alon and Frankl, Turán graphs with bounded matching number, arXiv:2210.15076v1, p. 5, Proposition 3.1

import Mathlib
import Definitions.Def_TuranMatching_ColorCritical_Setting

open Finset SimpleGraph

namespace TuranMatching.ColorCritical

theorem proposition_3_1 :
    ∃ n₀ : ℕ → ℕ, ∀ (W : Type) [Fintype W] (H : SimpleGraph W) (k : ℕ),
      IsColorCritical H → H.chromaticNumber = ((k + 1 : ℕ) : ℕ∞) → 2 < k + 1 →
      ∃ s₀ : ℕ, ∀ s : ℕ, s₀ < s → ∀ n : ℕ, n₀ s < n →
        (∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], H.Free G → TuranMatching.Clique.matchingNumber G ≤ s →
            #G.edgeFinset ≤ TuranMatching.Clique.gNum n k s) ∧
        ∃ (G : SimpleGraph (Fin n)) (_ : DecidableRel G.Adj), H.Free G ∧ TuranMatching.Clique.matchingNumber G ≤ s ∧
            #G.edgeFinset = TuranMatching.Clique.gNum n k s := by sorry

end TuranMatching.ColorCritical
