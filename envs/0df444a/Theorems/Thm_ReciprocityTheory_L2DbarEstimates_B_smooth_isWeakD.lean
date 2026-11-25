-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_B_smooth_isWeakD
-- name    : ReciprocityTheory.L2DbarEstimates.B.smooth_isWeakD
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T14:27:23.228999+00:00
-- url     : https://prove2.me/theorems/a50a2dc9-ae4d-59b3-9ad5-d0dfacd576cb
-- title:
--   B: smooth is Weak D
-- statement:
--   The B construction uses the smooth is Weak D property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Mollifiers/FderivMollApply.lean#L73-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Mollifiers/FderivMollApply.lean#L73-L111

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Mollifiers_HasCompactSupport
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Mollifiers_FderivMollApply
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

theorem ReciprocityTheory.L2DbarEstimates.B.smooth_isWeakD (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] : SmoothWeakSt E μ := by sorry
