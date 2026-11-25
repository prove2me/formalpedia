-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_hyq_contDiffAt_of_holo
-- name    : ReciprocityTheory.L2DbarEstimates.Y.hyq_contDiffAt_of_holo
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T16:20:11.602021+00:00
-- url     : https://prove2.me/theorems/51d6acf2-3255-4e8b-967e-d2c7a01fd4a6
-- title:
--   Y: hyq cont Diff At of holo
-- statement:
--   The Y construction uses the hyq cont Diff At of holo property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/ContDiffAtSectionFrameQuotient.lean#L50-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/ContDiffAtSectionFrameQuotient.lean#L50-L52

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatLoc
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatNull
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_HoloSmooth
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_EventuallyDifferentiableAtOfContDiffAt
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_ContDiffAtSectionFrameQuotient
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology WeightedAtlas Metric
open scoped ContDiff ENNReal Pointwise Matrix
noncomputable section
universe u
variable {n : ℕ} {Y : Type u} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]

theorem ReciprocityTheory.L2DbarEstimates.Y.hyq_contDiffAt_of_holo {g : V n → ℂ} {U : Set (V n)} (hU : IsOpen U)
    (hg : DifferentiableOn ℂ g U) {c : V n} (hc : c ∈ U) : ContDiffAt ℝ ∞ g c := by sorry
