-- Prove2me | Theorems.Thm_RobustPower_AdaptGap_eq_5_2_doubled_feasible
-- name    : RobustPower.AdaptGap.eq_5_2_doubled_feasible
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T01:53:07.822853+00:00
-- url     : https://prove2.me/theorems/3e58340b-bc2e-4d37-9b2a-cf9225835ed8
-- title:
--   Equation (5.2) — doubling center-scenario decisions gives a robust solution
-- statement:
--   In the same nonnegative symmetric scenario model, let $(x,y(\cdot))$ be any feasible adaptive decision and let $\omega^0$ realize the point of symmetry. Then the doubled decisions are feasible in the static robust problem:
--
--   $$2x\in D_{I_1},\qquad 2y(\omega^0)\in D_{I_2},\qquad A(2x)+B(2y(\omega^0))\ge b(\omega)\quad\text{for all }\omega\in\Omega.$$
--
--   The claim includes preservation of the integer coordinates and is the feasibility step used in Theorem 5.1.
-- source:
--   Bertsimas & Goyal, On the Power of Robust Solutions in Two-Stage Stochastic and Adaptive Optimization Problems, authors' manuscript (MIT DSpace) of Math. Oper. Res. DOI 10.1287/moor.1090.0440, pp. 28–29, (5.2) and the following claim

import Mathlib
import Definitions.Def_RobustPower_AdaptGap_Problems

namespace RobustPower.AdaptGap

/-- (5.2) and the p. 29 claim: doubling the center-scenario decisions is robust feasible. -/
theorem eq_5_2_doubled_feasible {m n₁ n₂ : ℕ} {Ω : Type*}
    (A : Matrix (Fin m) (Fin n₁) ℝ) (B : Matrix (Fin m) (Fin n₂) ℝ)
    (b : Ω → Fin m → ℝ) (d : Ω → Fin n₂ → ℝ)
    (I₁ : Set (Fin n₁)) (I₂ : Set (Fin n₂))
    (x : Fin n₁ → ℝ) (y : Ω → Fin n₂ → ℝ) (ω₀ : Ω)
    (hb : ∀ ω, 0 ≤ b ω) (hd : ∀ ω, 0 ≤ d ω)
    (hfeas : AdaptFeasible A B b I₁ I₂ x y)
    (hcenter : RobustPower.StochGap.IsSymmetricAbout (scenarioSet b d) (b ω₀, d ω₀)) :
    RobustPower.StochGap.RobFeasible A B b I₁ I₂ ((2 : ℝ) • x) ((2 : ℝ) • y ω₀) := by sorry

end RobustPower.AdaptGap
