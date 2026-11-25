-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_weight_nsmul_eq_mul
-- name    : ReciprocityTheory.L2DbarEstimates.Y.weight_nsmul_eq_mul
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T16:08:50.906508+00:00
-- url     : https://prove2.me/theorems/b64bed53-0756-5602-947f-39ceb3ff5245
-- title:
--   Y: weight nsmul eq mul
-- statement:
--   The Y construction uses the weight nsmul eq mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/DifferentiableAtLocalCoordinates.lean#L80-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/DifferentiableAtLocalCoordinates.lean#L80-L84

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatCalc
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_DifferentiableAtLocalCoordinates
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology WeightedAtlas Asymptotics
open scoped ContDiff ENNReal Pointwise Matrix
noncomputable section
universe u
variable {n : ℕ} {Y : Type*} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]

theorem ReciprocityTheory.L2DbarEstimates.Y.weight_nsmul_eq_mul (A : WeightedAtlas n Y ι La) (la : La) (m : ℕ) (i : ι) (y : Y)
    (hi : y ∈ (A.chart i).source) : A.ph (m • la) i y = m * A.ph la i y := by sorry
