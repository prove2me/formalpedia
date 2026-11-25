-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_L2DbarEstimates_Y_WeightedAtlas_CutData_eventually___zero_71899b15eb44
-- name    : P2M_ReciprocityTheory_L2DbarEstimates_Y_WeightedAtlas_CutData_eventually___zero_71899b15eb44
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T05:18:41.351629+00:00
-- url     : https://prove2.me/theorems/e4833708-c058-4db4-9694-4a974ac87ed8
-- title:
--   P2 M Reciprocity Theory L2 Dbar Estimates Y Weighted Atlas Cut Data eventually   zero 71899b15eb44: P2 M Reciprocity Theory L2 Dbar Estimates Y Weighted Atlas Cut Data eventually   zero 71899b15eb44
-- statement:
--   The P2 M Reciprocity Theory L2 Dbar Estimates Y Weighted Atlas Cut Data eventually   zero 71899b15eb44 construction uses the P2 M Reciprocity Theory L2 Dbar Estimates Y Weighted Atlas Cut Data eventually   zero 71899b15eb44 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/AApproxJ.lean#L65-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/AApproxJ.lean#L65-L71

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_AApproxF
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_AApproxJ
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
  (A : WeightedAtlas n Y ι La)
variable {A}
open ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas.CutData
variable {Sf : Finset Y} (D : CutData A Sf)

theorem P2M_ReciprocityTheory_L2DbarEstimates_Y_WeightedAtlas_CutData_eventually___zero_71899b15eb44 {P : Y} (hP : P ∈ Sf) (j : ι) {y : Y} (hj : y ∈ (A.chart j).source)
    (hy : y ∉ D.K P) : ∀ᶠ v in 𝓝 (A.chart j y), D.χ P ((A.chart j).symm v) = 0 := by sorry

alias «ReciprocityTheory».«L2DbarEstimates».«Y».«WeightedAtlas».«CutData».«eventually_χ_zero» := P2M_ReciprocityTheory_L2DbarEstimates_Y_WeightedAtlas_CutData_eventually___zero_71899b15eb44
