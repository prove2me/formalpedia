-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_WeightedAtlas_setLIntegral_biUnion_le
-- name    : ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas.setLIntegral_biUnion_le
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T11:01:51.246423+00:00
-- url     : https://prove2.me/theorems/f675eec7-208e-50b6-9183-217a1ed945b6
-- title:
--   Weighted Atlas: set LIntegral bi Union le
-- statement:
--   The Weighted Atlas construction uses the set LIntegral bi Union le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/SetLIntegralBiUnionLe.lean#L30-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/SetLIntegralBiUnionLe.lean#L30-L38

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_ZLocLower
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_SetLIntegralBiUnionLe
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
open scoped ContDiff ENNReal Pointwise Matrix
noncomputable section
open ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas
variable {n : ℕ} {Y : Type*} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]

theorem ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas.setLIntegral_biUnion_le {α κ : Type*} [MeasurableSpace α] (μ : Measure α)
    (F : Finset κ) (U : κ → Set α) (G : α → ℝ≥0∞) :
    ∫⁻ y in ⋃ P ∈ F, U P, G y ∂μ ≤ ∑ P ∈ F, ∫⁻ y in U P, G y ∂μ := by sorry
