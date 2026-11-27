-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_WeightedAtlas_CutData_dbar_eq_zero
-- name    : ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas.CutData.dbar_eq_zero
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T14:28:36.225637+00:00
-- url     : https://prove2.me/theorems/236b520b-62cc-5674-aeb7-daef07ae8ad7
-- title:
--   Cut Data: dbar eq zero
-- statement:
--   The Cut Data construction uses the dbar eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/AApproxK.lean#L20-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/AApproxK.lean#L20-L54

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_AApproxJ
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_AApproxK
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology Complex Metric Set
open scoped ContDiff ENNReal
noncomputable section
open ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas
variable {n : ℕ} {Y : Type*} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]
  {A : WeightedAtlas n Y ι La}
open ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas.CutData
variable {Sf : Finset Y} (D : CutData A Sf)

theorem ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas.CutData.dbar_eq_zero (la' : La) (c : Y → ℂ) (j : ι) {y : Y} (hj : y ∈ (A.chart j).source)
    (hT : y ∉ ⋃ P ∈ Sf, D.T P) (ξ : Fin n → ℂ) :
    A.dbarAt j (A.F0 la' Sf A.pick D.χ c) y ξ = 0 := by sorry
