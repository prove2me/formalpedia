-- Prove2me | Theorems.Thm_VanderbeiLP_StrictComp_strong_duality
-- name    : VanderbeiLP.StrictComp.strong_duality
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-01T17:22:49.904976+00:00
-- url     : https://prove2.me/theorems/9bc7de99-93cc-455c-9e39-6e87b28707a5
-- title:
--   Theorem 5.2 — Strong Duality Theorem
-- statement:
--   Consider the standard-form linear program "maximize $c^T x$ subject to $Ax \le b$, $x \ge 0$" with $A \in \mathbb{R}^{m \times n}$, $b \in \mathbb{R}^m$, $c \in \mathbb{R}^n$, and its dual "minimize $b^T y$ subject to $A^T y \ge c$, $y \ge 0$". If the primal has an optimal solution $x^* = (x^*_1, \dots, x^*_n)$, then the dual also has an optimal solution $y^* = (y^*_1, \dots, y^*_m)$ such that
--
--   $$\sum_{j=1}^n c_j x^*_j = \sum_{i=1}^m b_i y^*_i. \qquad (5.2)$$
--
--   There is no gap between the optimal primal and dual values. Together with weak duality this makes a pair of feasible points with equal objective values a certificate of optimality for both.
--
--   **Formalization Note** Optimality is attainment: $x^*$ is primal feasible with $c^T x \le c^T x^*$ for every primal feasible $x$, and the conclusion asserts a dual feasible $y^*$ with $b^T y^* \le b^T y$ for every dual feasible $y$.
-- source:
--   Vanderbei, Linear Programming: Foundations and Extensions, 4th ed., Springer 2014, p. 57, Theorem 5.2, Eq. (5.2) (PDF p. 73)

import Mathlib
import Definitions.Def_VanderbeiLP_StrictComp_PrimalDualPair

open Matrix

namespace VanderbeiLP.StrictComp

/-- **Vanderbei, Theorem 5.2 (p. 57).** Strong duality: if the primal has an optimal solution
`x*`, then the dual has an optimal solution `y*` with `Σⱼ cⱼx*ⱼ = Σᵢ bᵢy*ᵢ` (5.2). -/
theorem strong_duality {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) (xstar : Fin n → ℝ) (hx : PrimalOptimal A b c xstar) :
    ∃ ystar : Fin m → ℝ, DualOptimal A b c ystar ∧ c ⬝ᵥ xstar = b ⬝ᵥ ystar := by sorry

end VanderbeiLP.StrictComp
