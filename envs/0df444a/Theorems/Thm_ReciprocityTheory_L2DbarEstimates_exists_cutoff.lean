-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_exists_cutoff
-- name    : ReciprocityTheory.L2DbarEstimates.exists_cutoff
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T14:28:46.994947+00:00
-- url     : https://prove2.me/theorems/126c8fff-d4c8-4b4b-bfbd-4b8d3ccd17ee
-- title:
--   L2 Dbar Estimates: exists cutoff
-- statement:
--   The L2 Dbar Estimates construction uses the exists cutoff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/ChartDerivatives/ExistsChartPartition.lean#L159-L171
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/ChartDerivatives/ExistsChartPartition.lean#L159-L171

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

theorem ReciprocityTheory.L2DbarEstimates.exists_cutoff {M : Type*} [TopologicalSpace M] [T2Space M] (n : ℕ) (z : M → V n) (hz : IsLocalHomeomorph z) (K U : Set M) (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ η : M → ℝ, SmoothR n z η ∧ HasCompactSupport η ∧ tsupport η ⊆ U ∧
      (∀ x, 0 ≤ η x ∧ η x ≤ 1) ∧ ∀ x ∈ K, η x = 1 := by sorry
