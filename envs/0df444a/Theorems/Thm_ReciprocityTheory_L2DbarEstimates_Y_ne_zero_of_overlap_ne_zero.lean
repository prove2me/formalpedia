-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_ne_zero_of_overlap_ne_zero
-- name    : ReciprocityTheory.L2DbarEstimates.Y.ne_zero_of_overlap_ne_zero
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T16:10:25.487438+00:00
-- url     : https://prove2.me/theorems/1feb8e22-604e-4858-b042-953e8890d017
-- title:
--   Y: ne zero of overlap ne zero
-- statement:
--   The Y construction uses the ne zero of overlap ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/DifferentiableAtLocalCoordinates.lean#L94-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/DifferentiableAtLocalCoordinates.lean#L94-L99

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

theorem ReciprocityTheory.L2DbarEstimates.Y.ne_zero_of_overlap_ne_zero (A : WeightedAtlas n Y ι La) (la : La) (w0 : ι → Y → ℂ)
    (hw : A.IsSec la w0) (i j : ι) (y : Y)
    (hi : y ∈ (A.chart i).source) (hj : y ∈ (A.chart j).source) (h : w0 j y ≠ 0) :
    w0 i y ≠ 0 := by sorry
