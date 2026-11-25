-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_L2DbarEstimates_Y_WeightedAtlas_CutData_eventually___one_ae6e010d4c36
-- name    : P2M_ReciprocityTheory_L2DbarEstimates_Y_WeightedAtlas_CutData_eventually___one_ae6e010d4c36
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T05:17:27.933356+00:00
-- url     : https://prove2.me/theorems/22e6e877-92da-5f49-8143-2b17d69fd24d
-- title:
--   P2 M Reciprocity Theory L2 Dbar Estimates Y Weighted Atlas Cut Data eventually   one ae6e010d4c36: P2 M Reciprocity Theory L2 Dbar Estimates Y Weighted Atlas Cut Data eventually   one ae6e010d4c36
-- statement:
--   The P2 M Reciprocity Theory L2 Dbar Estimates Y Weighted Atlas Cut Data eventually   one ae6e010d4c36 construction uses the P2 M Reciprocity Theory L2 Dbar Estimates Y Weighted Atlas Cut Data eventually   one ae6e010d4c36 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/AApproxJ.lean#L73-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/AApproxJ.lean#L73-L89

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

theorem P2M_ReciprocityTheory_L2DbarEstimates_Y_WeightedAtlas_CutData_eventually___one_ae6e010d4c36 {P : Y} (j : ι) {y : Y} (hj : y ∈ (A.chart j).source)
    (hyP : y ∈ (A.chart (A.pick P)).source)
    (hb : A.chart (A.pick P) y ∈ ball (A.chart (A.pick P) P) (D.r1 P)) :
    ∀ᶠ v in 𝓝 (A.chart j y), (A.chart j).symm v ∈ (A.chart (A.pick P)).source ∧
      D.χ P ((A.chart j).symm v) = 1 := by sorry

alias «ReciprocityTheory».«L2DbarEstimates».«Y».«WeightedAtlas».«CutData».«eventually_χ_one» := P2M_ReciprocityTheory_L2DbarEstimates_Y_WeightedAtlas_CutData_eventually___one_ae6e010d4c36
