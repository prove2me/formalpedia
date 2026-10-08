-- Prove2me | Theorems.Thm_SelfDualLP_Regularity_theorem_2_iv
-- name    : SelfDualLP.Regularity.theorem_2_iv
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:58:15.080037+00:00
-- url     : https://prove2.me/theorems/2cb5ff50-a897-49f7-9a2c-fccb76e1673c
-- title:
--   Theorem 2(iv): zero optimal value and the complementarity identity
-- statement:
--   For arbitrary initial $x^0>0$, $s^0>0$, and $y^0$, the homogeneous program (HLP) has an optimal point with objective value zero. At every feasible point $(y,x,\tau,\theta,s,\kappa)$,
--   $$
--   ((x^0)^Ts^0+1)\theta=x^Ts+\tau\kappa.
--   $$
--   Because all terms on the right are nonnegative at feasible points, this identity also shows why an optimal point has $\theta=0$ and zero complementarity.
--
--   The identity connects the artificial objective with primal-dual complementarity and is used throughout the analysis of (HLP).
-- source:
--   Ye, Todd, Mizuno, An O(√nL)-Iteration Homogeneous and Self-Dual Linear Programming Algorithm, Math. Oper. Res. 19(1) (1994), p. 57, Theorem 2(iv); DOI 10.1287/moor.19.1.53

import Definitions.Def_SelfDualLP_Regularity_HLP

open Matrix

namespace SelfDualLP.Regularity

/-- Ye--Todd--Mizuno (1994), Theorem 2(iv), p. 57. -/
theorem theorem_2_iv {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (c : Fin n → ℝ)
    (x₀ : Fin n → ℝ) (y₀ : Fin m → ℝ) (s₀ : Fin n → ℝ)
    (hx₀ : ∀ j, 0 < x₀ j) (hs₀ : ∀ j, 0 < s₀ j) :
    (∃ w : HLPPoint m n,
      IsHLPOptimal A b c x₀ y₀ s₀ w ∧ HLPObjective x₀ s₀ w = 0) ∧
    ∀ w : HLPPoint m n, HLPFeasible A b c x₀ y₀ s₀ w →
      HLPObjective x₀ s₀ w = w.x ⬝ᵥ w.s + w.τ * w.κ := by sorry

end SelfDualLP.Regularity
