-- Prove2me | Theorems.Thm_PushInfoShare_assumption_1_relations
-- name    : PushInfoShare.assumption_1_relations
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:46:12.632665+00:00
-- url     : https://prove2.me/theorems/4664b9bd-cd2d-4d96-bc7c-5decaff6b5fb
-- title:
--   §3, p.8 — relations implied by Assumption 1 (corrected Assumption 1(b))
-- statement:
--   On a signal model, for each $i$,
--   $$E[\theta\mid Y_i]=\frac{t_iY_i}{\sigma^{-1}+t_i},\qquad E[\theta\mid Y_1,Y_2]=\frac{t_1Y_1+t_2Y_2}{\sigma^{-1}+t_1+t_2},\qquad E[Y_i^2]=\frac1{t_i}+\sigma,\qquad E[Y_1Y_2]=\sigma.$$
--   These are the moments that enter every expected profit, and they justify the retailer's forecast.
--
--   Differences from the source:
--   - correction: Assumption 1(b): E[Y1Y2|θ] = 0 → E[(Y1−θ)(Y2−θ)|θ] = 0; reason: the printed form gives E[Y1Y2] = 0, while the printed relations give E[Y1Y2] = E[Y2 E[θ|Y2]] = σ > 0, so with σ > 0 no model satisfies it; the corrected form is the one the normal-normal example of p.8 satisfies
--   - reading: E[Yi|Y3−i] = E[θ|Y3−i] is listed as implied by Assumption 1 (p.8) → it is a hypothesis of the signal model (field cross_forecast); reason: it needs E[Yi|θ,Y3−i] = θ, which conditional uncorrelatedness alone does not obviously give; it is exactly what the equilibrium uses, and no independence assumption is added
--   - encoding: t_i = 1/E[V(Y_i|θ)] → t_i = 1/E[(Y_i−θ)²]; reason: equal under Assumption 1(a)
--   - encoding: manufacturers 1, 2 and the index 3 − i → Fin 2 and the index 1 - i; reason: Lean indexing; same instances
--   - generalization: the four displayed relations of p.8 → the conclusion also contains E[Y1Y2] = σ; reason: this moment is what the corrected (b) contributes to expected profits; dropping it gives the source's list
-- source:
--   Jain, Sharing Demand Information with Retailer under Upstream Competition, SSRN:3388957 (PDF of 2021-04-25), §3, relations after Assumption 1, p.8

import Mathlib
import Definitions.Def_PushInfoShare_IsSignalModel
import Definitions.Def_PushInfoShare_precision

open MeasureTheory

namespace PushInfoShare

/-- The relations implied by Assumption 1, Jain, SSRN:3388957 (PDF of 2021-04-25), §3, p.8:
`E[θ | Yᵢ] = tᵢYᵢ/(σ⁻¹ + tᵢ)`, `E[θ | Y₁, Y₂] = (t₁Y₁ + t₂Y₂)/(σ⁻¹ + t₁ + t₂)`,
`E[Yᵢ²] = 1/tᵢ + σ`, and `E[Y₁Y₂] = σ`.

**Formalization Note.** `E[Yᵢ | Y₃₋ᵢ] = E[θ | Y₃₋ᵢ]` is a field of `IsSignalModel`, not a conclusion.
`E[Y₁Y₂] = σ` is not displayed on p.8; it is what the corrected Assumption 1(b) contributes to
expected profits, and the paper's own relations imply it. -/
theorem assumption_1_relations {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {θ : Ω → ℝ} {Y : Fin 2 → Ω → ℝ} {σ : ℝ} (hM : IsSignalModel μ θ Y σ) (i : Fin 2) :
    μ[θ | MeasurableSpace.comap (Y i) inferInstance] =ᵐ[μ]
        (fun ω => precision μ θ Y i * Y i ω / (σ⁻¹ + precision μ θ Y i)) ∧
      μ[θ | MeasurableSpace.comap (fun ω => (Y 0 ω, Y 1 ω)) inferInstance] =ᵐ[μ]
        (fun ω => (precision μ θ Y 0 * Y 0 ω + precision μ θ Y 1 * Y 1 ω) /
          (σ⁻¹ + precision μ θ Y 0 + precision μ θ Y 1)) ∧
      ∫ ω, Y i ω ^ 2 ∂μ = 1 / precision μ θ Y i + σ ∧
      ∫ ω, Y 0 ω * Y 1 ω ∂μ = σ := by sorry

end PushInfoShare
