-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_hyq_contDiffAt_of_ev
-- name    : ReciprocityTheory.L2DbarEstimates.Y.hyq_contDiffAt_of_ev
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T16:18:48.263087+00:00
-- url     : https://prove2.me/theorems/fd4e2b8e-b533-4c13-b106-b7f36a21440f
-- title:
--   Y: hyq cont Diff At of ev
-- statement:
--   The Y construction uses the hyq cont Diff At of ev property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/ContDiffAtSectionFrameQuotient.lean#L54-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/ContDiffAtSectionFrameQuotient.lean#L54-L57

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

theorem ReciprocityTheory.L2DbarEstimates.Y.hyq_contDiffAt_of_ev {g : V n → ℂ} {c : V n}
    (hg : ∀ᶠ v in 𝓝 c, DifferentiableAt ℂ g v) : ContDiffAt ℝ ∞ g c := by sorry
