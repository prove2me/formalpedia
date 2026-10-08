-- Prove2me | Theorems.Thm_TuranMatching_Clique_lemma_2_2
-- name    : TuranMatching.Clique.lemma_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T02:30:01.035985+00:00
-- url     : https://prove2.me/theorems/714d5cd5-2161-4d29-bbb2-8f6450e5bac8
-- title:
--   Lemma 2.2 — for an extremal $G$ maximizing $\sum a_i^2$, at most one component of $G-B$ is not a single vertex
-- statement:
--   Throughout, $k\ge2$, $n\ge2s+1$, and $G$ is an **extremal** graph: a graph on $n$ vertices with clique number at most $k$ and matching number at most $s$ having the maximum possible number of edges among all such graphs. Let $B$ be an odd barrier of $G$ with value $s$, and suppose that the pair $(G,B)$ maximizes $\sum_i a_i^2$: for every extremal graph $G'$ and every odd barrier $B'$ of $G'$ with value $s$,
--   $$\sum_{A'\text{ component of }G'-B'}|A'|^2\ \le\ \sum_{A\text{ component of }G-B}|A|^2 .$$
--
--   Then $a_i=1$ for all $2\le i\le m$: of any two distinct components of $G-B$, at least one is a single vertex.
--
--   Together with the barrier relation this gives $a_1=2s-2b+1$, which feeds the case analysis.
--
--   **Formalization Note** The maximum of $\sum a_i^2$ in the paper is taken among all extremal graphs together with their sets $B$, since $B$ is chosen with $G$; the hypothesis quantifies over all such pairs. With the components unordered, "$a_i=1$ for $2\le i\le m$" is stated as "of two distinct components, one has size $1$". The paper says "every $k$"; the restriction $k\ge2$ is needed because $G(n,k,s)$ has $k-1$ classes of total size $s$, which is impossible for $k=1$ and $s>0$, and no graph on $n\ge1$ vertices has clique number at most $0$.
-- source:
--   Alon and Frankl, Turán graphs with bounded matching number, arXiv:2210.15076v1, p. 2, Lemma 2.2 (statement); p. 2, "Among all such graphs … Σ a_i² is maximum"; proof p. 3

import Mathlib
import Definitions.Def_TuranMatching_Clique_Setting

open Finset SimpleGraph

namespace TuranMatching.Clique

theorem lemma_2_2 (n k s : ℕ) (hk : 2 ≤ k) (hn : 2 * s + 1 ≤ n)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : G.IsExtremal (Admissible k s))
    (B : Finset (Fin n)) (hB : IsOddBarrier G B s)
    (hmax : ∀ (G' : SimpleGraph (Fin n)) [DecidableRel G'.Adj] (B' : Finset (Fin n)),
      G'.IsExtremal (Admissible k s) → IsOddBarrier G' B' s → compSqSum G' B' ≤ compSqSum G B) :
    ∀ c c' : (G.induce ((B : Set (Fin n))ᶜ)).ConnectedComponent,
      c ≠ c' → c.supp.ncard = 1 ∨ c'.supp.ncard = 1 := by sorry

end TuranMatching.Clique
