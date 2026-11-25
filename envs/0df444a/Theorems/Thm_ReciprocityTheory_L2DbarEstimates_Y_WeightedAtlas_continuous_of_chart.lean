-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_WeightedAtlas_continuous_of_chart
-- name    : ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas.continuous_of_chart
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T11:00:55.612267+00:00
-- url     : https://prove2.me/theorems/0733afdd-688f-440d-a5b4-65b2a6263701
-- title:
--   Weighted Atlas: continuous of chart
-- statement:
--   The Weighted Atlas construction uses the continuous of chart property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/AApproxB.lean#L68-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/AApproxB.lean#L68-L78

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_AApproxA
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_AApproxB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology
open scoped ContDiff ENNReal
noncomputable section
open ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas
variable {n : ℕ} {Y : Type*} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]
  (A : WeightedAtlas n Y ι La)

theorem ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas.continuous_of_chart {E : Type*} [TopologicalSpace E] (f : Y → E)
    (hf : ∀ i, ContinuousOn (f ∘ (A.chart i).symm) (A.chart i).target) : Continuous f := by sorry
