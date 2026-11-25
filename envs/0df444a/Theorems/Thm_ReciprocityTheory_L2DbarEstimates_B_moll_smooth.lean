-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_B_moll_smooth
-- name    : ReciprocityTheory.L2DbarEstimates.B.moll_smooth
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T14:27:27.857844+00:00
-- url     : https://prove2.me/theorems/21d74c8a-2c01-546f-9259-8c5a9a6e9cb6
-- title:
--   B: moll smooth
-- statement:
--   The B construction uses the moll smooth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Mollifiers/HasCompactSupport.lean#L34-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Mollifiers/HasCompactSupport.lean#L34-L36

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

theorem ReciprocityTheory.L2DbarEstimates.B.moll_smooth (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] : SmoothSt E μ := by sorry
