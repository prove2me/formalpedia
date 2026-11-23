-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_WeightedAtlas_nsq_eq_chart
-- name    : ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas.nsq_eq_chart
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T11:30:03.242315+00:00
-- url     : https://prove2.me/theorems/5b1a28aa-0d26-446e-8b12-b65334cba17d
-- title:
--   Weighted Atlas: nsq eq chart
-- statement:
--   The Weighted Atlas construction uses the nsq eq chart property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/LintegralBallRpowLtTop.lean#L16-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/LintegralBallRpowLtTop.lean#L16-L28

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FamilyLeCoords
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_JacobianInterpolationStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_LintegralBallRpowLtTop
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
open ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas
variable {n : ℕ} {Y : Type*} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]

theorem ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas.nsq_eq_chart (A : WeightedAtlas n Y ι La) {la : La} {s : ι → Y → ℂ} (hs : A.IsSec la s)
    {i : ι} {y : Y} (hy : y ∈ (A.chart i).source) :
    A.nsq la s y = ‖s i y‖ ^ 2 * Real.exp (-A.ph la i y) := by sorry
