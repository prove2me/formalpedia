-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_api_nsq_contOn
-- name    : ReciprocityTheory.L2DbarEstimates.Y.api_nsq_contOn
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T14:29:03.835536+00:00
-- url     : https://prove2.me/theorems/a0b0fc59-3cc5-4650-b595-a4606b1daaee
-- title:
--   Y: api nsq cont On
-- statement:
--   The Y construction uses the api nsq cont On property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/APrimeI.lean#L116-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/APrimeI.lean#L116-L129

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

theorem ReciprocityTheory.L2DbarEstimates.Y.api_nsq_contOn (A : WeightedAtlas n Y ι La) {la : La} {U : Set Y} (hU : IsOpen U)
    {F : ι → Y → ℂ} (hFs : A.IsSecOn la U F) : ContinuousOn (A.nsq la F) U := by sorry
