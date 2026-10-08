-- Prove2me | Theorems.Thm_TuranMatching_Clique_lemma_2_1
-- name    : TuranMatching.Clique.lemma_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T02:29:44.035913+00:00
-- url     : https://prove2.me/theorems/d3d41762-71a6-400a-a07e-aa157986cdb2
-- title:
--   Lemma 2.1 — in an extremal graph, two non-adjacent vertices of an odd barrier $B$ have the same neighbourhood
-- statement:
--   Throughout, $k\ge2$, $n\ge2s+1$, and $G$ is an **extremal** graph: a graph on $n$ vertices with clique number at most $k$ and matching number at most $s$ having the maximum possible number of edges among all such graphs. Let $B$ be an odd barrier of $G$ with value $s$: every component $A_i$ of $G-B$ is odd and $|B|+\sum_i(|A_i|-1)/2=s$. As in the opening of §2, choose $(G,B)$ to maximize $\sum_i|A_i|^2$ among all such extremal graph and barrier pairs.
--
--   Then every two non-adjacent vertices $u,v\in B$ have the same neighbourhood:
--   $$u,v\in B,\ uv\notin E(G)\ \Longrightarrow\ N(u)=N(v).$$
--
--   This is the Zykov symmetrization step of the proof of Theorem 1.1; it makes the graph induced on $B$ complete multipartite.
--
--   **Formalization Note** Extremality is Mathlib's `IsExtremal` for the admissibility property. The maximality hypothesis ranges over graph–barrier pairs. The barrier value is the paper's $s$, not $\nu(G)$. The condition $u\ne v$ is implicit: a vertex is never adjacent to itself, and the conclusion is trivial for $u=v$. The paper says "every $k$"; the restriction $k\ge2$ is needed because $G(n,k,s)$ has $k-1$ classes of total size $s$, which is impossible for $k=1$ and $s>0$, and no graph on $n\ge1$ vertices has clique number at most $0$.
-- source:
--   Alon and Frankl, Turán graphs with bounded matching number, arXiv:2210.15076v1, p. 2, Lemma 2.1

import Mathlib
import Definitions.Def_TuranMatching_Clique_Setting

open Finset SimpleGraph

namespace TuranMatching.Clique

theorem lemma_2_1 (n k s : ℕ) (hk : 2 ≤ k) (hn : 2 * s + 1 ≤ n)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : G.IsExtremal (Admissible k s))
    (B : Finset (Fin n)) (hB : IsOddBarrier G B s)
    (hmax : ∀ (G' : SimpleGraph (Fin n)) [DecidableRel G'.Adj] (B' : Finset (Fin n)),
      G'.IsExtremal (Admissible k s) → IsOddBarrier G' B' s → compSqSum G' B' ≤ compSqSum G B) :
    ∀ u ∈ B, ∀ v ∈ B, ¬ G.Adj u v → G.neighborSet u = G.neighborSet v := by sorry

end TuranMatching.Clique
