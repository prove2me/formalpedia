-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_WeightedAtlas_aap_continuous_nsq
-- name    : ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas.aap_continuous_nsq
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T11:00:13.972498+00:00
-- url     : https://prove2.me/theorems/0226f13a-5b95-52b9-b4cc-8e343f5c3e94
-- title:
--   Weighted Atlas: aap continuous nsq
-- statement:
--   The Weighted Atlas construction uses the aap continuous nsq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/AApproxL.lean#L16-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/AApproxL.lean#L16-L47

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_AApproxK
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_AApproxL
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology Complex Metric Set
open scoped ContDiff ENNReal
noncomputable section
open ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas
variable {n : ℕ} {Y : Type*} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]
  (A : WeightedAtlas n Y ι La)

theorem ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas.aap_continuous_nsq (la : La) (u : ι → Y → ℂ)
    (hcoc : ∀ i j y, y ∈ (A.chart i).source → y ∈ (A.chart j).source → u i y = A.g la i j y * u j y)
    (hc : ∀ i, ContinuousOn (u i ∘ (A.chart i).symm) (A.chart i).target) :
    Continuous (A.nsq la u) := by sorry
