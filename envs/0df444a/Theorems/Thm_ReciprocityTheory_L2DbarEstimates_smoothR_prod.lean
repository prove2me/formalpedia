-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_smoothR_prod
-- name    : ReciprocityTheory.L2DbarEstimates.smoothR_prod
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T11:01:17.376649+00:00
-- url     : https://prove2.me/theorems/1197f2c6-59e9-5af4-b653-dde0d26be411
-- title:
--   L2 Dbar Estimates: smooth R prod
-- statement:
--   The L2 Dbar Estimates construction uses the smooth R prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/ChartDerivatives/ExistsChartPartition.lean#L14-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/ChartDerivatives/ExistsChartPartition.lean#L14-L24

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

theorem ReciprocityTheory.L2DbarEstimates.smoothR_prod {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) {ι : Type*}
    (s : Finset ι) (f : ι → M → ℝ) (hf : ∀ i ∈ s, SmoothR n z (f i)) :
    SmoothR n z (fun x => ∏ i ∈ s, f i x) := by sorry
