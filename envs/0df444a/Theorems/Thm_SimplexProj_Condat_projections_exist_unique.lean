-- Prove2me | Theorems.Thm_SimplexProj_Condat_projections_exist_unique
-- name    : SimplexProj.Condat.projections_exist_unique
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-01T23:10:25.838852+00:00
-- url     : https://prove2.me/theorems/b84bc65c-98c1-4a7d-a174-7ffe00cedc59
-- title:
--   The projections onto the simplex and the $\ell_1$ ball exist and are unique
-- statement:
--   Let $N \ge 1$, $a > 0$, and $y \in \mathbb{R}^N$. Let $\Delta$ be the simplex of radius $a$ and $B$ the $\ell_1$ ball of radius $a$. Then $y$ has exactly one Euclidean projection onto $\Delta$ and exactly one Euclidean projection onto $B$:
--
--   $$\exists!\, x \in \mathbb{R}^N,\ x = P_\Delta(y) \qquad\text{and}\qquad \exists!\, x \in \mathbb{R}^N,\ x = P_B(y).$$
--
--   Condat states this in the introduction ("These two projections are well defined and unique, since $\Delta$ and $B$ are closed and convex sets"); it makes $P_\Delta$ and $P_B$ functions, which every later statement of the paper uses.
--
--   **Formalization Note.** "$x = P_\Delta(y)$" is the predicate `IsSimplexProjection a y x`, and similarly for $B$. The hypotheses $N \ge 1$ and $a > 0$ are the paper's standing assumptions (Sect. 1).
-- source:
--   Condat, Fast Projection onto the Simplex and the ℓ1 Ball, HAL hal-01056171v2, p. 2, Sect. 1

import Mathlib
import Definitions.Def_SimplexProj_Condat_IsSimplexProjection
import Definitions.Def_SimplexProj_Condat_IsL1Projection

namespace SimplexProj.Condat

/-- Condat, Sect. 1, p. 2: the Euclidean projections `P_Δ(y)` and `P_B(y)` onto the simplex and
the `ℓ1` ball of radius `a` are well defined and unique. Standing assumptions of p. 1:
`N ≥ 1`, `a > 0`. -/
theorem projections_exist_unique (N : ℕ) (hN : 1 ≤ N) (a : ℝ) (ha : 0 < a) (y : Fin N → ℝ) :
    (∃! x : Fin N → ℝ, IsSimplexProjection a y x) ∧ (∃! x : Fin N → ℝ, IsL1Projection a y x) := by sorry

end SimplexProj.Condat
