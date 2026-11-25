-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_exists_chart_bump
-- name    : ReciprocityTheory.L2DbarEstimates.exists_chart_bump
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T11:01:44.03906+00:00
-- url     : https://prove2.me/theorems/b04f697f-e9b4-51e1-bde4-cf1a866b8409
-- title:
--   L2 Dbar Estimates: exists chart bump
-- statement:
--   The L2 Dbar Estimates construction uses the exists chart bump property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/ChartDerivatives/ExistsChartPartition.lean#L38-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/ChartDerivatives/ExistsChartPartition.lean#L38-L98

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

theorem ReciprocityTheory.L2DbarEstimates.exists_chart_bump {M : Type*} [TopologicalSpace M] [T2Space M] (n : ℕ) (z : M → V n)
    (hz : IsLocalHomeomorph z) (U : Set M) (hU : IsOpen U) (x : M) (hx : x ∈ U) :
    ∃ (e : OpenPartialHomeomorph M (V n)) (ψ : M → ℝ),
      IsChart n z e ∧ SmoothR n z ψ ∧ HasCompactSupport ψ ∧ tsupport ψ ⊆ e.source ∩ U ∧
      (∀ y, 0 ≤ ψ y ∧ ψ y ≤ 1) ∧ ∀ᶠ y in 𝓝 x, ψ y = 1 := by sorry
