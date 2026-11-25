-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_L2DbarEstimates_Y_WeightedAtlas_CutData___supp_82118ed35144
-- name    : P2M_ReciprocityTheory_L2DbarEstimates_Y_WeightedAtlas_CutData___supp_82118ed35144
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T05:18:55.663959+00:00
-- url     : https://prove2.me/theorems/3b9bc33d-8bbe-4d7e-9eac-38f5b06eb469
-- title:
--   P2 M Reciprocity Theory L2 Dbar Estimates Y Weighted Atlas Cut Data   supp 82118ed35144: P2 M Reciprocity Theory L2 Dbar Estimates Y Weighted Atlas Cut Data   supp 82118ed35144
-- statement:
--   The P2 M Reciprocity Theory L2 Dbar Estimates Y Weighted Atlas Cut Data   supp 82118ed35144 construction uses the P2 M Reciprocity Theory L2 Dbar Estimates Y Weighted Atlas Cut Data   supp 82118ed35144 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/AApproxJ.lean#L58-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/AApproxJ.lean#L58-L59

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

theorem P2M_ReciprocityTheory_L2DbarEstimates_Y_WeightedAtlas_CutData___supp_82118ed35144 (P : Y) (y : Y) (hy : D.χ P y ≠ 0) : y ∈ D.K P := by sorry

alias «ReciprocityTheory».«L2DbarEstimates».«Y».«WeightedAtlas».«CutData».«χ_supp» := P2M_ReciprocityTheory_L2DbarEstimates_Y_WeightedAtlas_CutData___supp_82118ed35144
