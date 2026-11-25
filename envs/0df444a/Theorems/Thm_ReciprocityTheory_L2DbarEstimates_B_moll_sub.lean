-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_B_moll_sub
-- name    : ReciprocityTheory.L2DbarEstimates.B.moll_sub
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T14:27:17.214799+00:00
-- url     : https://prove2.me/theorems/38b5e021-2010-5549-aa9b-36aa5df75528
-- title:
--   B: moll sub
-- statement:
--   The B construction uses the moll sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Mollifiers/HasCompactSupport.lean#L65-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Mollifiers/HasCompactSupport.lean#L65-L74

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Mollifiers_MollifierL2LocTendsto
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Mollifiers_HasCompactSupport
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.B
open MeasureTheory Filter Topology Set Metric
open scoped Convolution ContDiff ENNReal Pointwise

theorem ReciprocityTheory.L2DbarEstimates.B.moll_sub (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] (K : Kernel E μ) {u u' : E → ℂ} (hu : LocallyIntegrable u μ)
    (hu' : LocallyIntegrable u' μ) : moll K (u - u') = moll K u - moll K u' := by sorry
