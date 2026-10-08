-- Prove2me | Theorems.Thm_SelfDualLP_Complexity_theorem_2_ii
-- name    : SelfDualLP.Complexity.theorem_2_ii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:57:59.127989+00:00
-- url     : https://prove2.me/theorems/b339d46e-ddef-424d-a95a-379e38d5d175
-- title:
--   Theorem 2 (ii) — $(y^0,x^0,1,1,s^0,1)$ is a strictly feasible point of (HLP)
-- statement:
--   Let $A\in\mathbb R^{m\times n}$, $b\in\mathbb R^m$, $c\in\mathbb R^n$, and let $x^0>0$, $s^0>0$ and $y^0$ be the starting triple from which (HLP) is built. Then (HLP) has the strictly feasible point
--   $$
--   y=y^0,\quad x=x^0>0,\quad \tau=1,\quad \theta=1,\quad s=s^0>0,\quad \kappa=1,
--   $$
--   that is, this point lies in $\mathcal F_h^0$.
--
--   This is what lets the algorithm start at a known interior point without any big-$M$ parameter; under the choice (7) it is the initial iterate $(0,e,1,1,e,1)$.
-- source:
--   Ye, Todd, Mizuno, An O(√nL)-Iteration Homogeneous and Self-Dual Linear Programming Algorithm, Math. Oper. Res. 19(1) (1994), p. 57, Theorem 2 (ii)

import Mathlib
import Definitions.Def_SelfDualLP_Complexity_HLP

open Matrix

namespace SelfDualLP.Complexity

/-- Theorem 2 (ii) (p. 57). For any `x⁰ > 0`, `s⁰ > 0` and `y⁰`, (HLP) has the strictly
feasible point `(y, x, τ, θ, s, κ) = (y⁰, x⁰, 1, 1, s⁰, 1)`. -/
theorem theorem_2_ii {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (x0 : Fin n → ℝ) (y0 : Fin m → ℝ) (s0 : Fin n → ℝ)
    (hx0 : ∀ j, 0 < x0 j) (hs0 : ∀ j, 0 < s0 j) :
    HLPStrictlyFeasible A b c x0 y0 s0 ⟨y0, x0, 1, 1, s0, 1⟩ := by sorry

end SelfDualLP.Complexity
