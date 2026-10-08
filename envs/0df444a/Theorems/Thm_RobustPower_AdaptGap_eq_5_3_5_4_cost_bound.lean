-- Prove2me | Theorems.Thm_RobustPower_AdaptGap_eq_5_3_5_4_cost_bound
-- name    : RobustPower.AdaptGap.eq_5_3_5_4_cost_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T01:52:58.647052+00:00
-- url     : https://prove2.me/theorems/20e9403a-225a-44d2-b5a4-dc35a9939757
-- title:
--   Equations (5.3)–(5.4) — cost of the doubled solution
-- statement:
--   In the nonnegative symmetric scenario model, let $(x,y(\cdot))$ be any feasible adaptive decision and let $\omega^0$ realize the point of symmetry. The worst-case cost of the doubled static decision is bounded by four times the worst-case cost of the original adaptive decision:
--
--   $$c^T(2x)+\sup_{\omega\in\Omega}d(\omega)^T(2y(\omega^0))\le4\left(c^Tx+\sup_{\omega\in\Omega}d(\omega)^Ty(\omega)\right).$$
--
--   This estimate supplies the explicit factor four in Theorem 5.1 and applies to every feasible adaptive decision, without an attainment assumption.
-- source:
--   Bertsimas & Goyal, On the Power of Robust Solutions in Two-Stage Stochastic and Adaptive Optimization Problems, authors' manuscript (MIT DSpace) of Math. Oper. Res. DOI 10.1287/moor.1090.0440, p. 29, (5.3)–(5.4)

import Mathlib
import Definitions.Def_RobustPower_AdaptGap_Problems

namespace RobustPower.AdaptGap

/-- Inequalities (5.3)–(5.4), p. 29, for every feasible adaptive solution. -/
theorem eq_5_3_5_4_cost_bound {m n₁ n₂ : ℕ} {Ω : Type*}
    (A : Matrix (Fin m) (Fin n₁) ℝ) (B : Matrix (Fin m) (Fin n₂) ℝ)
    (b : Ω → Fin m → ℝ) (c : Fin n₁ → ℝ) (d : Ω → Fin n₂ → ℝ)
    (I₁ : Set (Fin n₁)) (I₂ : Set (Fin n₂))
    (x : Fin n₁ → ℝ) (y : Ω → Fin n₂ → ℝ) (ω₀ : Ω)
    (hc : 0 ≤ c) (hb : ∀ ω, 0 ≤ b ω) (hd : ∀ ω, 0 ≤ d ω)
    (hfeas : AdaptFeasible A B b I₁ I₂ x y)
    (hcenter : RobustPower.StochGap.IsSymmetricAbout (scenarioSet b d) (b ω₀, d ω₀)) :
    robCost c d ((2 : ℝ) • x) ((2 : ℝ) • y ω₀) ≤
      (4 : EReal) * adaptCost c d x y := by sorry

end RobustPower.AdaptGap
