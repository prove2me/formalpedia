-- Prove2me | Theorems.Thm_RobustPower_AdaptGap_eq_5_1_adapt_cost
-- name    : RobustPower.AdaptGap.eq_5_1_adapt_cost
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T01:53:04.909099+00:00
-- url     : https://prove2.me/theorems/8dd6ec45-837e-4f86-83d5-1ca6b3dd8029
-- title:
--   Equation (5.1) — center-scenario adaptive cost bound
-- statement:
--   In the two-stage adaptive problem, suppose the nonnegative scenario set is symmetric about the scenario $(b(\omega^0),d(\omega^0))$. Let $d^h$ be the coordinatewise upper endpoint of the cost vectors. For every feasible adaptive decision $(x,y(\cdot))$,
--
--   $$c^Tx+\left(\frac{d^h}{2}\right)^Ty(\omega^0)\le c^Tx+\sup_{\omega\in\Omega}d(\omega)^Ty(\omega).$$
--
--   The inequality measures how the center scenario controls the second-stage cost of any feasible adaptive policy; it does not require an optimal policy to exist.
-- source:
--   Bertsimas & Goyal, On the Power of Robust Solutions in Two-Stage Stochastic and Adaptive Optimization Problems, authors' manuscript (MIT DSpace) of Math. Oper. Res. DOI 10.1287/moor.1090.0440, p. 28, (5.1)

import Mathlib
import Definitions.Def_RobustPower_AdaptGap_Problems

open Matrix

namespace RobustPower.AdaptGap

/-- Inequality (5.1), p. 28, for an arbitrary feasible adaptive solution. -/
theorem eq_5_1_adapt_cost {m n₁ n₂ : ℕ} {Ω : Type*}
    (A : Matrix (Fin m) (Fin n₁) ℝ) (B : Matrix (Fin m) (Fin n₂) ℝ)
    (b : Ω → Fin m → ℝ) (c : Fin n₁ → ℝ) (d : Ω → Fin n₂ → ℝ)
    (I₁ : Set (Fin n₁)) (I₂ : Set (Fin n₂))
    (x : Fin n₁ → ℝ) (y : Ω → Fin n₂ → ℝ) (ω₀ : Ω)
    (hc : 0 ≤ c) (hb : ∀ ω, 0 ≤ b ω) (hd : ∀ ω, 0 ≤ d ω)
    (hfeas : AdaptFeasible A B b I₁ I₂ x y)
    (hcenter : RobustPower.StochGap.IsSymmetricAbout (scenarioSet b d) (b ω₀, d ω₀)) :
    (((c ⬝ᵥ x + (costUpper d / 2) ⬝ᵥ y ω₀ : ℝ) : EReal) ≤
      adaptCost c d x y) := by sorry

end RobustPower.AdaptGap
