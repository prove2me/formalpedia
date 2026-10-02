-- Prove2me | Theorems.Thm_VanderbeiLP_StrictComp_complementary_slackness
-- name    : VanderbeiLP.StrictComp.complementary_slackness
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-01T17:26:23.900487+00:00
-- url     : https://prove2.me/theorems/9dc13e47-5646-403b-aa9a-e487391bea33
-- title:
--   Theorem 5.3 — Complementary Slackness Theorem
-- statement:
--   Consider the standard-form linear program "maximize $c^T x$ subject to $Ax \le b$, $x \ge 0$" with $A \in \mathbb{R}^{m \times n}$, $b \in \mathbb{R}^m$, $c \in \mathbb{R}^n$, and its dual "minimize $b^T y$ subject to $A^T y \ge c$, $y \ge 0$". Suppose $x = (x_1, \dots, x_n)$ is primal feasible and $y = (y_1, \dots, y_m)$ is dual feasible, and let
--
--   - $w_i = b_i - \sum_j a_{ij} x_j$ ($i = 1, \dots, m$) be the corresponding primal slack variables,
--   - $z_j = \sum_i y_i a_{ij} - c_j$ ($j = 1, \dots, n$) be the corresponding dual slack variables.
--
--   Then $x$ and $y$ are optimal for their respective problems if and only if
--
--   $$x_j z_j = 0 \ \ (j = 1, \dots, n), \qquad w_i y_i = 0 \ \ (i = 1, \dots, m). \qquad (5.7)$$
--
--   The theorem turns optimality into a finite system of equations, which is how an optimal dual solution is recovered from an optimal primal one.
-- source:
--   Vanderbei, Linear Programming: Foundations and Extensions, 4th ed., Springer 2014, p. 63, Theorem 5.3, Eq. (5.7) (PDF p. 79)

import Mathlib
import Definitions.Def_VanderbeiLP_StrictComp_PrimalDualPair

open Matrix

namespace VanderbeiLP.StrictComp

/-- **Vanderbei, Theorem 5.3 (p. 63).** Complementary slackness: for primal feasible `x` with
slack `w = b - Ax` and dual feasible `y` with slack `z = Aᵀy - c`, `x` and `y` are optimal
for their respective problems iff `xⱼzⱼ = 0` for all `j` and `wᵢyᵢ = 0` for all `i` (5.7). -/
theorem complementary_slackness {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) (x : Fin n → ℝ) (y : Fin m → ℝ)
    (hx : PrimalFeasible A b x) (hy : DualFeasible A c y) :
    (PrimalOptimal A b c x ∧ DualOptimal A b c y) ↔
      ((∀ j, x j * dualSlack A c y j = 0) ∧ ∀ i, primalSlack A b x i * y i = 0) := by sorry

end VanderbeiLP.StrictComp
