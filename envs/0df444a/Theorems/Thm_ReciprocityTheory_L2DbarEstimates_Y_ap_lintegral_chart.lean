-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_ap_lintegral_chart
-- name    : ReciprocityTheory.L2DbarEstimates.Y.ap_lintegral_chart
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T14:29:03.616274+00:00
-- url     : https://prove2.me/theorems/ba230680-814f-4689-af80-0c4d0d167ab1
-- title:
--   Y: ap lintegral chart
-- statement:
--   The Y construction uses the ap lintegral chart property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/APrimeI.lean#L14-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/APrimeI.lean#L14-L41

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_APrimeW
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_HoloSmooth
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_APrimeI
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
variable {n : ℕ} {Y : Type*} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]

theorem ReciprocityTheory.L2DbarEstimates.Y.ap_lintegral_chart (A : WeightedAtlas n Y ι La) (i : ι) (g : Y → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ y in (A.chart i).source, g y ∂A.mu =
      ∫⁻ v in (A.chart i).target, g ((A.chart i).symm v) *
        ENNReal.ofReal (Real.exp (A.ph A.kap i ((A.chart i).symm v))) := by sorry
