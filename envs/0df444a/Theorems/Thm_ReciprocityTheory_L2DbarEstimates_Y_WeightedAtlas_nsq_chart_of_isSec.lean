-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_WeightedAtlas_nsq_chart_of_isSec
-- name    : ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas.nsq_chart_of_isSec
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T11:02:39.027425+00:00
-- url     : https://prove2.me/theorems/cc84e04d-f7d0-4c5d-8803-918e3596e4e0
-- title:
--   Weighted Atlas: nsq chart of is Sec
-- statement:
--   The Weighted Atlas construction uses the nsq chart of is Sec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/AApproxB.lean#L42-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/AApproxB.lean#L42-L44

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

theorem ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas.nsq_chart_of_isSec (la : La) (s : ι → Y → ℂ) (hs : A.IsSec la s) (i : ι) {y : Y}
    (hy : y ∈ (A.chart i).source) : A.nsq la s y = ‖s i y‖ ^ 2 * Real.exp (-A.ph la i y) := by sorry
