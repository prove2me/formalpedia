-- Prove2me | Theorems.Thm_SelfDualLP_Complexity_theorem_2_iv
-- name    : SelfDualLP.Complexity.theorem_2_iv
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:59:02.636696+00:00
-- url     : https://prove2.me/theorems/1ccb6393-dc91-4466-a443-f6e7144c0ab3
-- title:
--   Theorem 2 (iv) — the optimal value of (HLP) is zero and $((x^0)^Ts^0+1)\theta=x^Ts+\tau\kappa$ on $\mathcal F_h$
-- statement:
--   Let (HLP) be built from data $A,b,c$ and a starting triple with $x^0>0$, $s^0>0$ and arbitrary $y^0$. Then
--
--   1. the optimal value of (HLP) is zero: (HLP) has an optimal solution, and its objective value $((x^0)^Ts^0+1)\theta$ is $0$;
--   2. for every feasible point $(y,x,\tau,\theta,s,\kappa)\in\mathcal F_h$,
--   $$
--   ((x^0)^Ts^0+1)\,\theta=x^Ts+\tau\kappa .
--   $$
--
--   The identity ties the artificial variable $\theta$ to the complementarity gap, so driving the gap to zero drives $\theta$ to zero; in particular $\theta=\mu$ on $\mathcal N(\beta)$ under (7).
-- source:
--   Ye, Todd, Mizuno, An O(√nL)-Iteration Homogeneous and Self-Dual Linear Programming Algorithm, Math. Oper. Res. 19(1) (1994), p. 57, Theorem 2 (iv)

import Mathlib
import Definitions.Def_SelfDualLP_Complexity_HLP

open Matrix

namespace SelfDualLP.Complexity

/-- Theorem 2 (iv) (p. 57). For any `x⁰ > 0`, `s⁰ > 0` and `y⁰`: the optimal value of (HLP) is
zero (there is an optimal solution and its objective value `((x⁰)ᵀs⁰ + 1)θ` is `0`), and every
feasible point `(y, x, τ, θ, s, κ) ∈ 𝓕_h` satisfies `((x⁰)ᵀs⁰ + 1)θ = xᵀs + τκ`. -/
theorem theorem_2_iv {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (x0 : Fin n → ℝ) (y0 : Fin m → ℝ) (s0 : Fin n → ℝ)
    (hx0 : ∀ j, 0 < x0 j) (hs0 : ∀ j, 0 < s0 j) :
    (∃ z : HLPPoint m n, HLPOptimal A b c x0 y0 s0 z ∧ hlpObjective x0 s0 z = 0) ∧
    ∀ z : HLPPoint m n, HLPFeasible A b c x0 y0 s0 z →
      (x0 ⬝ᵥ s0 + 1) * z.θ = z.x ⬝ᵥ z.s + z.τ * z.κ := by sorry

end SelfDualLP.Complexity
