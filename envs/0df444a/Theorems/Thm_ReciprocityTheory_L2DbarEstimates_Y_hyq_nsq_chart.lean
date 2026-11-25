-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_hyq_nsq_chart
-- name    : ReciprocityTheory.L2DbarEstimates.Y.hyq_nsq_chart
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T16:18:19.970122+00:00
-- url     : https://prove2.me/theorems/82970d61-ab85-42fa-a814-51769970261f
-- title:
--   Y: hyq nsq chart
-- statement:
--   The Y construction uses the hyq nsq chart property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/ContDiffAtSectionFrameQuotient.lean#L18-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/ContDiffAtSectionFrameQuotient.lean#L18-L30

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

theorem ReciprocityTheory.L2DbarEstimates.Y.hyq_nsq_chart (A : WeightedAtlas n Y ι La) (la : La) (s : ι → Y → ℂ) (i : ι) (y : Y)
    (hi : y ∈ (A.chart i).source)
    (hs : s i y = A.g la i (A.pick y) y * s (A.pick y) y) :
    A.nsq la s y = ‖s i y‖ ^ 2 * Real.exp (-A.ph la i y) := by sorry
