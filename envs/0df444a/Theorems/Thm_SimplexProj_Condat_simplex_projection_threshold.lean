-- Prove2me | Theorems.Thm_SimplexProj_Condat_simplex_projection_threshold
-- name    : SimplexProj.Condat.simplex_projection_threshold
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-01T23:16:41.650891+00:00
-- url     : https://prove2.me/theorems/3c505ad7-81ed-4978-8e7a-b37178fc5729
-- title:
--   Proposition 2.2 — the simplex projection is a thresholding
-- statement:
--   Let $N \ge 1$, $a > 0$, $y \in \mathbb{R}^N$, and let $x = P_\Delta(y)$ be the Euclidean projection of $y$ onto the simplex $\Delta$ of radius $a$. Then there exists a unique $\tau \in \mathbb{R}$ such that
--
--   $$x_n = \max\{y_n - \tau, 0\} \qquad \text{for all } n = 1, \dots, N.$$
--
--   This is Proposition 2.2 of Condat (Eq. (6)). It reduces computing $P_\Delta(y)$ to finding the single number $\tau$, which all the algorithms of the paper do; $\tau$ is then characterized by $\sum_{n} \max\{y_n - \tau, 0\} = a$.
--
--   **Formalization Note.** $x = P_\Delta(y)$ is the predicate `IsSimplexProjection a y x`. The hypothesis $a > 0$ is needed for uniqueness of $\tau$.
-- source:
--   Condat, Fast Projection onto the Simplex and the ℓ1 Ball, HAL hal-01056171v2, p. 2, Proposition 2.2, Eq. (6)

import Mathlib
import Definitions.Def_SimplexProj_Condat_IsSimplexProjection

namespace SimplexProj.Condat

/-- Condat, Proposition 2.2 (p. 2, Eq. (6)): if `x = P_Δ(y)` is the Euclidean projection of `y`
onto the simplex of radius `a`, there is a unique `τ ∈ ℝ` with `x_n = max {y_n - τ, 0}` for all
`n`. Standing assumptions of p. 1: `N ≥ 1`, `a > 0`. -/
theorem simplex_projection_threshold (N : ℕ) (hN : 1 ≤ N) (a : ℝ) (ha : 0 < a)
    (y x : Fin N → ℝ) (hx : IsSimplexProjection a y x) :
    ∃! τ : ℝ, ∀ n, x n = max (y n - τ) 0 := by sorry

end SimplexProj.Condat
