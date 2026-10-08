-- Prove2me | Theorems.Thm_SelfDualLP_Output_theorem_2_iv
-- name    : SelfDualLP.Output.theorem_2_iv
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:27:25.78786+00:00
-- url     : https://prove2.me/theorems/77c077ee-dda6-4af7-ab0c-319a2b5f52c9
-- title:
--   Theorem 2 (iv) — the optimal value of (HLP) is zero and ((x⁰)ᵀs⁰ + 1)θ = xᵀs + τκ on F_h
-- statement:
--   Let $A\in\mathbb R^{m\times n}$, $b\in\mathbb R^m$, $c\in\mathbb R^n$, and let $x^0>0$, $s^0>0$ (componentwise) and $y^0$ be arbitrary. Consider the homogeneous self-dual program (HLP) built from these data. Then:
--
--   1. the optimal value of (HLP) is zero, i.e. (HLP) has an optimal solution and its objective value $((x^0)^Ts^0+1)\theta$ is $0$;
--   2. every feasible point $(y,x,\tau,\theta,s,\kappa)\in\mathcal F_h$ satisfies
--   $$
--   \bigl((x^0)^Ts^0+1\bigr)\theta=x^Ts+\tau\kappa .
--   $$
--
--   Under the choice (7) the identity reads $(n+1)\theta=x^Ts+\tau\kappa$, i.e. $\theta=\mu$ on $\mathcal F_h$; in particular every optimal solution has $\theta=0$.
-- source:
--   Ye, Todd, Mizuno, An O(√nL)-Iteration Homogeneous and Self-Dual Linear Programming Algorithm, Math. Oper. Res. 19(1) (1994), p. 57, Theorem 2 (iv); DOI 10.1287/moor.19.1.53

import Mathlib
import Definitions.Def_SelfDualLP_Complexity_LPData
import Definitions.Def_SelfDualLP_Output_HLP
import Definitions.Def_SelfDualLP_Output_Neighborhood
import Definitions.Def_SelfDualLP_Output_PCSequence

open Matrix

namespace SelfDualLP.Output

/-- Theorem 2 (iv) (p. 57). For any `x⁰ > 0`, `s⁰ > 0` and `y⁰`: the optimal value of (HLP) is
zero (there is an optimal solution and its objective value `((x⁰)ᵀs⁰ + 1)θ` is `0`), and every
feasible point `(y, x, τ, θ, s, κ) ∈ 𝓕_h` satisfies `((x⁰)ᵀs⁰ + 1)θ = xᵀs + τκ`. -/
theorem theorem_2_iv {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (x0 : Fin n → ℝ) (y0 : Fin m → ℝ) (s0 : Fin n → ℝ)
    (hx0 : ∀ j, 0 < x0 j) (hs0 : ∀ j, 0 < s0 j) :
    (∃ z : HLPPoint m n, HLPOptimal A b c x0 y0 s0 z ∧ hlpObjective x0 s0 z = 0) ∧
    ∀ z : HLPPoint m n, HLPFeasible A b c x0 y0 s0 z →
      (x0 ⬝ᵥ s0 + 1) * z.θ = z.x ⬝ᵥ z.s + z.τ * z.κ := by sorry
end SelfDualLP.Output
