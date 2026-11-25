-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_transition_nsmul_eq_pow
-- name    : ReciprocityTheory.L2DbarEstimates.Y.transition_nsmul_eq_pow
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T16:09:06.003118+00:00
-- url     : https://prove2.me/theorems/9ac9ffdc-2b54-5cbf-a59e-7bc951d07ed1
-- title:
--   Y: transition nsmul eq pow
-- statement:
--   The Y construction uses the transition nsmul eq pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/DifferentiableAtLocalCoordinates.lean#L67-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/DifferentiableAtLocalCoordinates.lean#L67-L72

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

theorem ReciprocityTheory.L2DbarEstimates.Y.transition_nsmul_eq_pow (A : WeightedAtlas n Y ι La) (la : La) (m : ℕ) (i j : ι) (y : Y)
    (hi : y ∈ (A.chart i).source) (hj : y ∈ (A.chart j).source) :
    A.g (m • la) i j y = A.g la i j y ^ m := by sorry
