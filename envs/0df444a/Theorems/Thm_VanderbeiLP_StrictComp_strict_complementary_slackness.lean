-- Prove2me | Theorems.Thm_VanderbeiLP_StrictComp_strict_complementary_slackness
-- name    : VanderbeiLP.StrictComp.strict_complementary_slackness
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-01T18:20:30.942523+00:00
-- url     : https://prove2.me/theorems/e8ad897c-2aa3-408c-a691-3acf943ec7f9
-- title:
--   Theorem 10.7 — Strict Complementary Slackness Theorem
-- statement:
--   Consider the linear program with explicit slacks
--
--   $$\text{maximize } c^T x \ \text{ subject to } Ax + w = b,\ x, w \ge 0 \qquad (10.9)$$
--
--   and its dual
--
--   $$\text{minimize } b^T y \ \text{ subject to } A^T y - z = c,\ y, z \ge 0, \qquad (10.10)$$
--
--   with $A \in \mathbb{R}^{m \times n}$, $b \in \mathbb{R}^m$, $c \in \mathbb{R}^n$. If the primal problem has an optimal solution, then there are an optimal primal solution $(x^*, w^*)$ and an optimal dual solution $(y^*, z^*)$ such that
--
--   $$x^* + z^* > 0 \qquad \text{and} \qquad y^* + w^* > 0,$$
--
--   where $\xi > 0$ means that every component of $\xi$ is strictly positive.
--
--   By complementary slackness (Theorem 5.3), for every optimal pair $x^*_j z^*_j = 0$ and $y^*_i w^*_i = 0$. The theorem says that the optimal pair can be chosen so that in each complementary pair exactly one member vanishes: the complementary slackness is strict. This is the Goldman–Tucker theorem (1956), written for Vanderbei's inequality-form pair.
--
--   **Formalization Note** "Optimal" means feasible and attaining the maximum (primal) or the minimum (dual) over the feasible set. The dual optimum is part of the conclusion: only a primal optimal solution is assumed. The slacks are $w^* = b - Ax^*$ and $z^* = A^T y^* - c$. The book's remark after the theorem cites "the complementary slackness theorem (Theorem 5.1)"; the complementary slackness theorem is Theorem 5.3.
-- source:
--   Vanderbei, Linear Programming: Foundations and Extensions, 4th ed., Springer 2014, p. 149, Theorem 10.7 (PDF p. 162); Eqs. (10.9)–(10.10), p. 147; footnote 2, p. 148

import Mathlib
import Definitions.Def_VanderbeiLP_StrictComp_PrimalDualPair

open Matrix

namespace VanderbeiLP.StrictComp

/-- **Vanderbei, Theorem 10.7 (p. 149), Strict Complementary Slackness Theorem.** If the LP
(10.9) has an optimal solution, then there are a primal optimal `x*` (slack `w* = b - Ax*`) and
a dual optimal `y*` (slack `z* = Aᵀy* - c`) with `x* + z* > 0` and `y* + w* > 0`
componentwise. -/
theorem strict_complementary_slackness {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (c : Fin n → ℝ) (hopt : ∃ x : Fin n → ℝ, PrimalOptimal A b c x) :
    ∃ (xstar : Fin n → ℝ) (ystar : Fin m → ℝ),
      PrimalOptimal A b c xstar ∧ DualOptimal A b c ystar ∧
      (∀ j, 0 < xstar j + dualSlack A c ystar j) ∧
      (∀ i, 0 < ystar i + primalSlack A b xstar i) := by sorry

end VanderbeiLP.StrictComp
