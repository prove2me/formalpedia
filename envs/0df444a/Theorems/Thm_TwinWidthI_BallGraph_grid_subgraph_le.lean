-- Prove2me | Theorems.Thm_TwinWidthI_BallGraph_grid_subgraph_le
-- name    : TwinWidthI.BallGraph.grid_subgraph_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:45:41.490058+00:00
-- url     : https://prove2.me/theorems/ae0e6964-32ef-4092-84d6-f27aad352099
-- title:
--   §4.2, p. 3:15 — every subgraph of the $d$-dimensional $n$-grid has twin-width at most $3d$
-- statement:
--   Let $d,n$ be positive integers, let $S\subseteq[n]^d$, and let $H$ be a subgraph of the $d$-dimensional $n$-grid $P^d_n$ with vertex set $S$: every edge of $H$ is an edge of $P^d_n$ with both ends in $S$. Then
--   $$\operatorname{tww}(H)\le 3d .$$
--
--   So bounded twin-width of grids is not lost by deleting vertices and edges, although bounded twin-width is in general not preserved under (non-induced) subgraphs (p. 3:13). The paper obtains it from the red bound of the proof of Theorem 4.3.
--
--   **Formalization Note.** "Subgraph" allows deleting vertices (the set $S$) and edges ($H\le P^d_n[S]$, Mathlib's order on graphs on the subtype of $S$). The hypotheses $1\le d$, $1\le n$ are those of Theorem 4.3, in whose context the sentence is stated.
-- source:
--   Bonnet, Kim, Thomassé and Watrigant, Twin-width I: Tractable FO Model Checking, J. ACM 69(1), Article 3 (2021), p. 3:15, §4.2, "it implies that the twin-width of any subgraph of the d-dimensional n-grid is bounded by 3d"

import Mathlib
import Definitions.Def_TwinWidthI_BallGraph_Setting

namespace TwinWidthI.BallGraph

/-- §4.2, p. 3:15: every subgraph of the d-dimensional n-grid (delete vertices outside `S`,
then edges) has twin-width at most `3d`. -/
theorem grid_subgraph_le (d n : ℕ) (hd : 1 ≤ d) (hn : 1 ≤ n) (S : Finset (Fin d → Fin n))
    (H : SimpleGraph S) (hH : H ≤ (grid d n).induce (S : Set (Fin d → Fin n))) :
    TwinWidthI.BoolWidth.TwinWidthLE H (3 * d) := by sorry

end TwinWidthI.BallGraph
