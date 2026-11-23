-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_exists_chart_partition
-- name    : ReciprocityTheory.L2DbarEstimates.exists_chart_partition
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T09:20:37.511009+00:00
-- url     : https://prove2.me/theorems/84330c8f-6f0a-4e2c-b0e3-277489436849
-- title:
--   L2 Dbar Estimates: exists chart partition
-- statement:
--   The L2 Dbar Estimates construction uses the exists chart partition property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/ChartDerivatives/ExistsChartPartition.lean#L100-L157
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/ChartDerivatives/ExistsChartPartition.lean#L100-L157

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_TsupportDbSubset
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_ExistsChartPartition
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates
open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal
noncomputable section

theorem ReciprocityTheory.L2DbarEstimates.exists_chart_partition {M : Type*} [TopologicalSpace M] [T2Space M] (n : ℕ) (z : M → V n) (hz : IsLocalHomeomorph z) (K U : Set M) (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ (N : ℕ) (e : Fin N → OpenPartialHomeomorph M (V n)) (χ : Fin N → M → ℝ),
      (∀ i, IsChart n z (e i)) ∧ (∀ i, SmoothR n z (χ i)) ∧ (∀ i, HasCompactSupport (χ i)) ∧
      (∀ i, tsupport (χ i) ⊆ (e i).source ∩ U) ∧ (∀ i x, 0 ≤ χ i x) ∧
      (∀ x, ∑ i, χ i x ≤ 1) ∧ (∀ x ∈ K, ∑ i, χ i x = 1) := by sorry
