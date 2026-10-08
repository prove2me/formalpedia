-- Prove2me | Theorems.Thm_TuranMatching_Clique_theorem_1_1
-- name    : TuranMatching.Clique.theorem_1_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T02:30:33.713981+00:00
-- url     : https://prove2.me/theorems/07f5176e-72d9-4272-b2d8-98df3c3f3a4f
-- title:
--   Theorem 1.1 — for $n\ge2s+1$ the maximum number of edges with clique number $\le k$ and matching number $\le s$ is $\max\{t(2s+1,k),g(n,k,s)\}$
-- statement:
--   Let $k\ge2$, $s\ge0$ and $n\ge2s+1$. Among all graphs on $n$ vertices with clique number at most $k$ and matching number at most $s$, the maximum possible number of edges is
--   $$\max\{\,t(2s+1,k),\ g(n,k,s)\,\}.$$
--   That is:
--
--   1. every such graph has at most $\max\{t(2s+1,k),g(n,k,s)\}$ edges, and
--   2. some such graph has exactly that many edges.
--
--   Here $t(2s+1,k)$ is the number of edges of the Turán graph $T(2s+1,k)$, and $g(n,k,s)$ is the number of edges of the complete $k$-partite graph $G(n,k,s)$ with $k-1$ balanced classes of total size $s$ and one class of size $n-s$.
--
--   The theorem is a common generalization of Turán's theorem (the matching condition is void when $n\le2s+1$) and of the Erdős–Gallai theorem on graphs with bounded matching number (the clique condition is void when $k\ge2s+1$).
--
--   **Formalization Note** Clique number at most $k$ is `CliqueFree (k + 1)`; the matching number is defined in the Setting as a maximum over matching subgraphs. The paper says "every $k$"; the restriction $k\ge2$ is needed because $G(n,k,s)$ has $k-1$ classes of total size $s$, which is impossible for $k=1$ and $s>0$, and no graph on $n\ge1$ vertices has clique number at most $0$. "Maximum" is formalized as an upper bound together with an attaining graph.
-- source:
--   Alon and Frankl, Turán graphs with bounded matching number, arXiv:2210.15076v1, p. 1, Theorem 1.1

import Mathlib
import Definitions.Def_TuranMatching_Clique_Setting

open Finset SimpleGraph

namespace TuranMatching.Clique

theorem theorem_1_1 (n k s : ℕ) (hk : 2 ≤ k) (hn : 2 * s + 1 ≤ n) :
    (∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], Admissible k s G →
        #G.edgeFinset ≤ max (turanNum (2 * s + 1) k) (gNum n k s)) ∧
    ∃ (G : SimpleGraph (Fin n)) (_ : DecidableRel G.Adj), Admissible k s G ∧
        #G.edgeFinset = max (turanNum (2 * s + 1) k) (gNum n k s) := by sorry

end TuranMatching.Clique
