-- Prove2me | Theorems.Thm_SimplexProj_Condat_l1_projection_from_simplex
-- name    : SimplexProj.Condat.l1_projection_from_simplex
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-01T23:42:12.931015+00:00
-- url     : https://prove2.me/theorems/8c7d1b26-f279-4672-ad27-e8b0684008d9
-- title:
--   Proposition 2.1 — projection onto the $\ell_1$ ball via the simplex
-- statement:
--   Let $N \ge 1$, $a > 0$, $y \in \mathbb{R}^N$, and write $|y| = (|y_1|, \dots, |y_N|)$. Let $x = P_\Delta(|y|)$ be the Euclidean projection of $|y|$ onto the simplex of radius $a$. Then the Euclidean projection of $y$ onto the $\ell_1$ ball $B$ of radius $a$ is
--
--   $$P_B(y) = \begin{cases} y, & \text{if } \sum_{n=1}^N |y_n| \le a, \\ (\operatorname{sgn}(y_1) x_1, \dots, \operatorname{sgn}(y_N) x_N), & \text{else,} \end{cases}$$
--
--   where $\operatorname{sgn}(t) = 1$ for $t > 0$, $\operatorname{sgn}(t) = -1$ for $t < 0$ and $\operatorname{sgn}(0) = 0$.
--
--   This is Proposition 2.1 of Condat (Eq. (4)); it is why an algorithm for the simplex also projects onto the $\ell_1$ ball.
--
--   **Formalization Note.** "$P_B(y) = w$" is the predicate `IsL1Projection a y w`; $\operatorname{sgn}$ is Mathlib's `Real.sign`, which has the same values (in particular `Real.sign 0 = 0`).
-- source:
--   Condat, Fast Projection onto the Simplex and the ℓ1 Ball, HAL hal-01056171v2, p. 2, Proposition 2.1, Eq. (4)

import Mathlib
import Definitions.Def_SimplexProj_Condat_IsSimplexProjection
import Definitions.Def_SimplexProj_Condat_IsL1Projection

namespace SimplexProj.Condat

/-- Condat, Proposition 2.1 (p. 2, Eq. (4)): with `x = P_Δ(|y|)` the projection of
`|y| = (|y_1|, …, |y_N|)` onto the simplex of radius `a`, the projection of `y` onto the `ℓ1`
ball of radius `a` is `y` if `∑ₙ |y_n| ≤ a` and `(sgn(y_1) x_1, …, sgn(y_N) x_N)` otherwise, with
`sgn 0 = 0` (Mathlib's `Real.sign`). Standing assumptions of p. 1: `N ≥ 1`, `a > 0`. -/
theorem l1_projection_from_simplex (N : ℕ) (hN : 1 ≤ N) (a : ℝ) (ha : 0 < a)
    (y x : Fin N → ℝ) (hx : IsSimplexProjection a (fun n => |y n|) x) :
    IsL1Projection a y
      (if ∑ n, |y n| ≤ a then y else fun n => Real.sign (y n) * x n) := by sorry

end SimplexProj.Condat
