-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_ChartNormSquare_nsq_eq_chart
-- name    : ReciprocityTheory.L2DbarEstimates.Y.ChartNormSquare.nsq_eq_chart
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T10:59:54.284015+00:00
-- url     : https://prove2.me/theorems/1e0b06ac-8b1d-5c56-ab94-e56d0f11488e
-- title:
--   Chart Norm Square: nsq eq chart
-- statement:
--   The Chart Norm Square construction uses the nsq eq chart property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/AExact.lean#L21-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/AExact.lean#L21-L37

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_GROWCountStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_AExact
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
open ReciprocityTheory.L2DbarEstimates.Y.ChartNormSquare
variable {n : ℕ} {Y : Type*} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]

theorem ReciprocityTheory.L2DbarEstimates.Y.ChartNormSquare.nsq_eq_chart (A : WeightedAtlas n Y ι La) (la : La) (F : ι → Y → ℂ) (hF : A.IsSec la F)
    (i : ι) (y : Y) (hy : y ∈ (A.chart i).source) :
    A.nsq la F y = ‖F i y‖ ^ 2 * Real.exp (-A.ph la i y) := by sorry
