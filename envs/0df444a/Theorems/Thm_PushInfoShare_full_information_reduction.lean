-- Prove2me | Theorems.Thm_PushInfoShare_full_information_reduction
-- name    : PushInfoShare.full_information_reduction
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:49:00.654994+00:00
-- url     : https://prove2.me/theorems/01d1873a-5d37-41a9-923a-f9d4d2651c07
-- title:
--   §4, p.11 — prices and orders under full information sharing (corrected: Assumption 1(b))
-- statement:
--   When both manufacturers share, in equilibrium
--   $$w_i^F=\frac{a}{2+\phi}+\frac{(2(1+\phi)+\phi s_{3-i})s_i}{4(1+\phi)^2-\phi^2s_1s_2}Y_i,\qquad q_i^F=\tfrac12\bigl(a-(1+\phi)w_i+\phi w_{3-i}+S_1Y_1+S_2Y_2\bigr).$$
--   With sharing on both sides the signaling distortion is absent, which makes this the reference case for the comparisons of §5.
--
--   Differences from the source:
--   - correction: Assumption 1(b): E[Y1Y2|θ] = 0 → E[(Y1−θ)(Y2−θ)|θ] = 0; reason: the printed form gives E[Y1Y2] = 0, while the printed relations give E[Y1Y2] = E[Y2 E[θ|Y2]] = σ > 0, so with σ > 0 no model satisfies it; the corrected form is the one the normal-normal example of p.8 satisfies
--   - reading: E[Yi|Y3−i] = E[θ|Y3−i] is listed as implied by Assumption 1 (p.8) → it is a hypothesis of the signal model (field cross_forecast); reason: it needs E[Yi|θ,Y3−i] = θ, which conditional uncorrelatedness alone does not obviously give; it is exactly what the equilibrium uses, and no independence assumption is added
--   - encoding: t_i = 1/E[V(Y_i|θ)] → t_i = 1/E[(Y_i−θ)²]; reason: equal under Assumption 1(a)
--   - encoding: manufacturers 1, 2 and the index 3 − i → Fin 2 and the index 1 - i; reason: Lean indexing; same instances
--   - encoding: Π_i = max over w_i of w_i E[q_i*], given i's information → ex-ante optimality over measurable f with f∘Y_i in L²; reason: pointwise optimality at almost every signal is the same condition for this quadratic payoff
--   - encoding: the retailer's forecast E[θ|δ1,δ2] (p.10) → S1 X1 + S2 X2, with X_j = Y_j if shared and the signal inferred from w_j otherwise; reason: this is the p.8 formula for E[θ|Y1,Y2] at the known or inferred signals; assumption_1_relations proves it
-- source:
--   Jain, Sharing Demand Information with Retailer under Upstream Competition, SSRN:3388957 (PDF of 2021-04-25), §4, reduction after Proposition 1, p.11

import Mathlib
import Definitions.Def_PushInfoShare_IsSignalModel
import Definitions.Def_PushInfoShare_accuracy
import Definitions.Def_PushInfoShare_IsLinearSeparatingEq

open MeasureTheory

namespace PushInfoShare

/-- The full-information reduction, Jain, SSRN:3388957 (PDF of 2021-04-25), §4, p.11: when both
manufacturers share, the equilibrium prices are
`wᵢᶠ = a/(2+φ) + (2(1+φ) + φs₃₋ᵢ)sᵢ/(4(1+φ)² − φ²s₁s₂) Yᵢ` and the orders are
`qᵢᶠ = ½(a − (1+φ)wᵢ + φw₃₋ᵢ + S₁Y₁ + S₂Y₂)`. -/
theorem full_information_reduction {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {θ : Ω → ℝ} {Y : Fin 2 → Ω → ℝ} {σ : ℝ} (hM : IsSignalModel μ θ Y σ) {a φ : ℝ} (hφ : 0 ≤ φ)
    {str : Profile} (hstr : IsLinearSeparatingEq μ θ Y σ a φ (fun _ => true) str) (i : Fin 2) :
    (∀ y : ℝ, str.α i + str.B i * y =
      a / (2 + φ) +
        (2 * (1 + φ) + φ * accuracy μ θ Y σ (1 - i)) * accuracy μ θ Y σ i /
          (4 * (1 + φ) ^ 2 - φ ^ 2 * accuracy μ θ Y σ 0 * accuracy μ θ Y σ 1) * y) ∧
      ∀ w y : Fin 2 → ℝ, str.q i w y =
        1 / 2 * (a - (1 + φ) * w i + φ * w (1 - i) +
          jointWeight μ θ Y σ 0 * y 0 + jointWeight μ θ Y σ 1 * y 1) := by sorry

end PushInfoShare
