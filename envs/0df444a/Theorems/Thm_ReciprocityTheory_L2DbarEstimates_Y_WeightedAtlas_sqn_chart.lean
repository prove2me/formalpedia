-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_WeightedAtlas_sqn_chart
-- name    : ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas.sqn_chart
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T13:32:24.835547+00:00
-- url     : https://prove2.me/theorems/dc465fbe-dfc2-41be-8c32-9d4b66c22d9c
-- title:
--   Weighted Atlas: sqn chart
-- statement:
--   The Weighted Atlas construction uses the sqn chart property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/AApproxB.lean#L46-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/AApproxB.lean#L46-L51

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_AApproxA
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_AApproxB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology
open scoped ContDiff ENNReal
noncomputable section
open ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas
variable {n : ℕ} {Y : Type*} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]
  (A : WeightedAtlas n Y ι La)

theorem ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas.sqn_chart {N : ℕ} (la : La) (w : Fin N → ι → Y → ℂ) (hw : ∀ k, A.IsSec la (w k)) (i : ι)
    {y : Y} (hy : y ∈ (A.chart i).source) :
    A.sqn la w y = (∑ k, ‖w k i y‖ ^ 2) * Real.exp (-A.ph la i y) := by sorry
