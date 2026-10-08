-- Prove2me | Theorems.Thm_TuranMatching_Clique_extremal_graphs_admissible
-- name    : TuranMatching.Clique.extremal_graphs_admissible
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T02:29:42.354758+00:00
-- url     : https://prove2.me/theorems/b5b2038d-9ff5-476e-92a7-c7cd35206189
-- title:
--   p. 1, Theorem 1.1 (lower bound); p. 5 — $G(n,k,s)$ and $T(2s+1,k)$ plus isolated vertices are admissible
-- statement:
--   Let $k\ge2$, $s\ge0$ and $n\ge 2s+1$. Then:
--
--   1. the graph $G(n,k,s)$ has clique number at most $k$ and matching number at most $s$;
--   2. there is a graph on $n$ vertices with clique number at most $k$ and matching number at most $s$ that has exactly $t(2s+1,k)$ edges.
--
--   Hence
--   $$\max\{t(2s+1,k),\,g(n,k,s)\}$$
--   is a lower bound for the maximum number of edges of an $n$-vertex graph with clique number at most $k$ and matching number at most $s$. This is the lower-bound half of Theorem 1.1; the natural witness for (2) is the Turán graph $T(2s+1,k)$ on $2s+1$ of the vertices with the remaining $n-2s-1$ vertices isolated.
--
--   **Formalization Note** The paper says "every $k$"; the restriction $k\ge2$ is needed because $G(n,k,s)$ has $k-1$ classes of total size $s$, which is impossible for $k=1$ and $s>0$, and no graph on $n\ge1$ vertices has clique number at most $0$.
-- source:
--   Alon and Frankl, Turán graphs with bounded matching number, arXiv:2210.15076v1, p. 1, Theorem 1.1 (the lower bound); p. 5, proof of Proposition 3.1, first two sentences

import Mathlib
import Definitions.Def_TuranMatching_Clique_Setting

open Finset SimpleGraph

namespace TuranMatching.Clique

theorem extremal_graphs_admissible (n k s : ℕ) (hk : 2 ≤ k) (hn : 2 * s + 1 ≤ n) :
    Admissible k s (bigGraph n k s) ∧
    ∃ (G : SimpleGraph (Fin n)) (_ : DecidableRel G.Adj), Admissible k s G ∧
        #G.edgeFinset = turanNum (2 * s + 1) k := by sorry

end TuranMatching.Clique
