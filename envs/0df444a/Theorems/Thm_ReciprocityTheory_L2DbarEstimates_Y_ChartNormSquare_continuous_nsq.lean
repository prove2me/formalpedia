-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_ChartNormSquare_continuous_nsq
-- name    : ReciprocityTheory.L2DbarEstimates.Y.ChartNormSquare.continuous_nsq
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T14:27:56.458279+00:00
-- url     : https://prove2.me/theorems/2d02e3bd-4e32-52f8-b55b-f83f43e8ed94
-- title:
--   Chart Norm Square: continuous nsq
-- statement:
--   The Chart Norm Square construction uses the continuous nsq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/AExact.lean#L39-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/AExact.lean#L39-L56

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

theorem ReciprocityTheory.L2DbarEstimates.Y.ChartNormSquare.continuous_nsq (A : WeightedAtlas n Y ι La) (la : La) (F : ι → Y → ℂ)
    (hF : A.IsSec la F) : Continuous (A.nsq la F) := by sorry
