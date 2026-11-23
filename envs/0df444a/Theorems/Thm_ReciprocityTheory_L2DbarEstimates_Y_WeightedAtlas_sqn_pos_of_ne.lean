-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_WeightedAtlas_sqn_pos_of_ne
-- name    : ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas.sqn_pos_of_ne
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:38:20.798255+00:00
-- url     : https://prove2.me/theorems/95ba244d-ef52-4278-9a7f-68148203cac7
-- title:
--   Weighted Atlas: sqn pos of ne
-- statement:
--   The Weighted Atlas construction uses the sqn pos of ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/SetLIntegralBiUnionLe.lean#L15-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/SetLIntegralBiUnionLe.lean#L15-L23

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_ZLocLower
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_SetLIntegralBiUnionLe
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

theorem ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas.sqn_pos_of_ne (A : WeightedAtlas n Y ι La) {la : La} {N : ℕ} {w : Fin N → ι → Y → ℂ}
    {y : Y} (h : ∃ k, w k (A.pick y) y ≠ 0) : 0 < A.sqn la w y := by sorry
