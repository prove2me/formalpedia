-- Prove2me | Theorems.Thm_VanderbeiLP_StrictComp_weak_duality
-- name    : VanderbeiLP.StrictComp.weak_duality
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-01T17:18:02.550334+00:00
-- url     : https://prove2.me/theorems/6561fcab-755e-445d-be70-71350e84584b
-- title:
--   Theorem 5.1 — Weak Duality Theorem
-- statement:
--   Consider the standard-form linear program "maximize $c^T x$ subject to $Ax \le b$, $x \ge 0$" with $A \in \mathbb{R}^{m \times n}$, $b \in \mathbb{R}^m$, $c \in \mathbb{R}^n$, and its dual "minimize $b^T y$ subject to $A^T y \ge c$, $y \ge 0$". If $x = (x_1, \dots, x_n)$ is feasible for the primal and $y = (y_1, \dots, y_m)$ is feasible for the dual, then
--
--   $$\sum_{j=1}^n c_j x_j \le \sum_{i=1}^m b_i y_i.$$
--
--   Every dual feasible point therefore certifies an upper bound on the primal objective, and every primal feasible point a lower bound on the dual objective.
-- source:
--   Vanderbei, Linear Programming: Foundations and Extensions, 4th ed., Springer 2014, p. 56, Theorem 5.1 (PDF p. 72)

import Mathlib
import Definitions.Def_VanderbeiLP_StrictComp_PrimalDualPair

open Matrix

namespace VanderbeiLP.StrictComp

/-- **Vanderbei, Theorem 5.1 (p. 56).** Weak duality: if `x` is primal feasible and `y` is
dual feasible, then `Σⱼ cⱼxⱼ ≤ Σᵢ bᵢyᵢ`. -/
theorem weak_duality {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) (x : Fin n → ℝ) (y : Fin m → ℝ)
    (hx : PrimalFeasible A b x) (hy : DualFeasible A c y) :
    c ⬝ᵥ x ≤ b ⬝ᵥ y := by sorry

end VanderbeiLP.StrictComp
