-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_L2DbarEstimates_Y_WeightedAtlas_CutData___smooth_e05dd90a1961
-- name    : P2M_ReciprocityTheory_L2DbarEstimates_Y_WeightedAtlas_CutData___smooth_e05dd90a1961
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T13:44:32.440618+00:00
-- url     : https://prove2.me/theorems/05704b17-efbe-4213-b256-b9668ad6f2ed
-- title:
--   P2 M Reciprocity Theory L2 Dbar Estimates Y Weighted Atlas Cut Data   smooth e05dd90a1961: P2 M Reciprocity Theory L2 Dbar Estimates Y Weighted Atlas Cut Data   smooth e05dd90a1961
-- statement:
--   The P2 M Reciprocity Theory L2 Dbar Estimates Y Weighted Atlas Cut Data   smooth e05dd90a1961 construction uses the P2 M Reciprocity Theory L2 Dbar Estimates Y Weighted Atlas Cut Data   smooth e05dd90a1961 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/AApproxJ.lean#L55-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/AApproxJ.lean#L55-L56

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

theorem P2M_ReciprocityTheory_L2DbarEstimates_Y_WeightedAtlas_CutData___smooth_e05dd90a1961 {P : Y} (hP : P ∈ Sf) : A.SmoothFn (D.χ P) := by sorry

alias «ReciprocityTheory».«L2DbarEstimates».«Y».«WeightedAtlas».«CutData».«χ_smooth» := P2M_ReciprocityTheory_L2DbarEstimates_Y_WeightedAtlas_CutData___smooth_e05dd90a1961
