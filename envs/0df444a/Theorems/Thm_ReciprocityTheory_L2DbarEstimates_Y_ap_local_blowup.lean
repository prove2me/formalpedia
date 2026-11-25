-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_ap_local_blowup
-- name    : ReciprocityTheory.L2DbarEstimates.Y.ap_local_blowup
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T14:29:18.566942+00:00
-- url     : https://prove2.me/theorems/064d66f2-3d98-5825-a8d5-f9065f625cdc
-- title:
--   Y: ap local blowup
-- statement:
--   The Y construction uses the ap local blowup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/APrimeLoc.lean#L59-L247
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/APrimeLoc.lean#L59-L247

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_APrimeA
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_APrimeB
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_APrimeLoc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology WeightedAtlas
open scoped ContDiff ENNReal
noncomputable section
set_option maxHeartbeats 800000

theorem ReciprocityTheory.L2DbarEstimates.Y.ap_local_blowup (n d : ℕ) (hd : 1 ≤ d) (hMVd : ∀ k, MVStatement k)
    (hMVI : MVIntStatement d) (U : Set (V n)) (hU : IsOpen U) (p : V n → V d)
    (hp : DifferentiableOn ℂ p U) (v0 : V n) (hv0 : v0 ∈ U) (hp0 : p v0 = 0)
    (hsurj : Function.Surjective (fderiv ℂ p v0)) :
    ∃ δ : ℝ, 0 < δ ∧ Metric.closedBall v0 δ ⊆ U ∧ ∀ M : ℝ, ∃ τ0 : ℝ, 0 < τ0 ∧
      ∀ τ : ℝ, 0 < τ → τ ≤ τ0 → ∀ u : V n → ℂ, DifferentiableOn ℂ u (Metric.ball v0 δ) →
        ENNReal.ofReal (M * ‖u v0‖ ^ 2) ≤
          ∫⁻ v in Metric.ball v0 δ, ENNReal.ofReal (‖u v‖ ^ 2 * (max (‖p v‖ ^ 2) τ) ^ (-(d : ℝ))) := by sorry
