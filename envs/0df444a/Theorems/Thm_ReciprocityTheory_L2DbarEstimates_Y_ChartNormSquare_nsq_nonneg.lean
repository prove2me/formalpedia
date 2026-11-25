-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_ChartNormSquare_nsq_nonneg
-- name    : ReciprocityTheory.L2DbarEstimates.Y.ChartNormSquare.nsq_nonneg
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T11:04:24.51635+00:00
-- url     : https://prove2.me/theorems/9f360ebc-7824-53d2-aab1-31ba4d9ecf61
-- title:
--   Chart Norm Square: nsq nonneg
-- statement:
--   The Chart Norm Square construction uses the nsq nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/AExact.lean#L58-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/AExact.lean#L58-L60

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

theorem ReciprocityTheory.L2DbarEstimates.Y.ChartNormSquare.nsq_nonneg (A : WeightedAtlas n Y ι La) (la : La) (F : ι → Y → ℂ) (y : Y) :
    0 ≤ A.nsq la F y := by sorry
