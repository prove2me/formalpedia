-- Prove2me | Theorems.Thm_TwinWidthI_BallGraph_theorem_4_3
-- name    : TwinWidthI.BallGraph.theorem_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:44:44.485287+00:00
-- url     : https://prove2.me/theorems/25de73e1-ed6d-480b-870e-e2612babe1c9
-- title:
--   Theorem 4.3, p. 3:15 — the $d$-dimensional $n$-grid has twin-width at most $3d$
-- statement:
--   Let $d,n$ be positive integers and let $P^d_n$ be the $d$-dimensional $n$-grid: the graph on $[n]^d$ in which $x$ and $y$ are adjacent if and only if $\sum_{i=1}^d|x_i-y_i|=1$. Then
--   $$\operatorname{tww}(P^d_n)\le 3d .$$
--
--   Rank-width and related width parameters are unbounded already on the $n\times n$ grid; twin-width stays bounded on grids of any fixed dimension. The bound is the stepping stone towards unit ball graphs (Theorem 4.5).
--
--   **Formalization Note.** $[n]^d$ is `Fin d → Fin n` and twin-width is the partition-form predicate `TwinWidthLE` of the Setting. The hypotheses $1\le d$, $1\le n$ are on the page.
-- source:
--   Bonnet, Kim, Thomassé and Watrigant, Twin-width I: Tractable FO Model Checking, J. ACM 69(1), Article 3 (2021), p. 3:15, Theorem 4.3

import Mathlib
import Definitions.Def_TwinWidthI_BallGraph_Setting

namespace TwinWidthI.BallGraph

/-- Theorem 4.3, p. 3:15: for positive integers `d`, `n`, the d-dimensional n-grid has
twin-width at most `3d`. -/
theorem theorem_4_3 (d n : ℕ) (hd : 1 ≤ d) (hn : 1 ≤ n) :
    TwinWidthI.BoolWidth.TwinWidthLE (grid d n) (3 * d) := by sorry

end TwinWidthI.BallGraph
