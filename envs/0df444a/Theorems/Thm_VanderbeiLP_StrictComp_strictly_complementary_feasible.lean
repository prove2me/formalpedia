-- Prove2me | Theorems.Thm_VanderbeiLP_StrictComp_strictly_complementary_feasible
-- name    : VanderbeiLP.StrictComp.strictly_complementary_feasible
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-01T18:00:55.947471+00:00
-- url     : https://prove2.me/theorems/b5ca56a3-2d8e-4872-8139-6dd7b40db97c
-- title:
--   Theorem 10.6 — strictly complementary feasible solutions
-- statement:
--   Consider the linear program with explicit slacks
--
--   $$\text{maximize } c^T x \ \text{ subject to } Ax + w = b,\ x, w \ge 0 \qquad (10.9)$$
--
--   and its dual
--
--   $$\text{minimize } b^T y \ \text{ subject to } A^T y - z = c,\ y, z \ge 0, \qquad (10.10)$$
--
--   with $A \in \mathbb{R}^{m \times n}$, $b \in \mathbb{R}^m$, $c \in \mathbb{R}^n$. If both the primal and the dual have feasible solutions, then there exist a primal feasible solution $(\bar x, \bar w)$ and a dual feasible solution $(\bar y, \bar z)$ such that
--
--   $$\bar x + \bar z > 0 \qquad \text{and} \qquad \bar y + \bar w > 0,$$
--
--   where $\xi > 0$ means that every component of the vector $\xi$ is strictly positive. Since all four vectors are nonnegative, this says that for each $j$ at least one of $\bar x_j$, $\bar z_j$ is positive, and for each $i$ at least one of $\bar y_i$, $\bar w_i$ is positive.
--
--   This is the feasible-solution version of strict complementarity; the Strict Complementary Slackness Theorem strengthens it to optimal solutions.
--
--   **Formalization Note** The slacks are determined by the solutions: $\bar w = b - A\bar x$ and $\bar z = A^T \bar y - c$.
-- source:
--   Vanderbei, Linear Programming: Foundations and Extensions, 4th ed., Springer 2014, p. 148, Theorem 10.6 and footnote 2 (PDF p. 161); Eqs. (10.9)–(10.10), p. 147

import Mathlib
import Definitions.Def_VanderbeiLP_StrictComp_PrimalDualPair

open Matrix

namespace VanderbeiLP.StrictComp

/-- **Vanderbei, Theorem 10.6 (p. 148).** If both the primal (10.9) and the dual (10.10) have
feasible solutions, then there are a primal feasible `x̄` (slack `w̄ = b - Ax̄`) and a dual
feasible `ȳ` (slack `z̄ = Aᵀȳ - c`) with `x̄ + z̄ > 0` and `ȳ + w̄ > 0` componentwise. -/
theorem strictly_complementary_feasible {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (c : Fin n → ℝ)
    (hP : ∃ x : Fin n → ℝ, PrimalFeasible A b x) (hD : ∃ y : Fin m → ℝ, DualFeasible A c y) :
    ∃ (xbar : Fin n → ℝ) (ybar : Fin m → ℝ),
      PrimalFeasible A b xbar ∧ DualFeasible A c ybar ∧
      (∀ j, 0 < xbar j + dualSlack A c ybar j) ∧
      (∀ i, 0 < ybar i + primalSlack A b xbar i) := by sorry

end VanderbeiLP.StrictComp
