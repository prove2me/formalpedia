-- Prove2me | Theorems.Thm_StrategyproofMinimax_Tree_sum_dist_level_one_ge
-- name    : StrategyproofMinimax.Tree.sum_dist_level_one_ge
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-01T22:15:08.952453+00:00
-- url     : https://prove2.me/theorems/3d33de1e-1ac4-4983-b597-fb2fd140e911
-- title:
--   Appendix B, p. 525 — pointwise bound on the distances to the m left vertices on level 1
-- statement:
--   Let $m\ge 2$ and $k\ge1$, and let $l^1_1,\dots,l^1_m$ be the left vertices on level 1 of the tree $G(m,k)$. For every point $y\in G$ (a vertex or a point inside an edge) with $d(y,l^0)\ge 1/2$,
--   $$\sum_{j=1}^{m} d(y,l^1_j)\ \ge\ m+(m-2)\cdot\tfrac12=\frac{3m-2}{2}.$$
--   This is the geometric fact behind the averaging step of the proof of Theorem 4.1: a facility far from $l^0$ is far from most of its children.
--
--   **Formalization Note.** The left vertices on level 1 are `vertex .left [j]`, `j : Fin m`, and $l^0$ is `vertex .left []`.
-- source:
--   Alon, Feldman, Procaccia, Tennenholtz, Strategyproof Approximation of the Minimax on Networks, Math. Oper. Res. 35(3) (2010), p. 525, Appendix B (display following Figure A.6)

import Mathlib
import Definitions.Def_StrategyproofMinimax_Tree_HardTree

namespace StrategyproofMinimax.Tree

/-- Appendix B, p. 525: for every point `y` of `G(m, k)` (vertex or edge point) with
`d(y, l⁰) ≥ 1/2`, the distances to the `m` left vertices `l¹₁, …, l¹ₘ` on level 1 satisfy
`∑ⱼ d(y, l¹ⱼ) ≥ m + (m − 2) · 1/2 = (3m − 2)/2`. -/
theorem sum_dist_level_one_ge {m k : ℕ} (hm : 2 ≤ m) (hk : 1 ≤ k) (y : HardTree m k)
    (hy : (1 : ℝ) / 2 ≤ dist y (vertex .left [])) :
    (3 * (m : ℝ) - 2) / 2 ≤ ∑ j : Fin m, dist y (vertex .left [j]) := by sorry

end StrategyproofMinimax.Tree
