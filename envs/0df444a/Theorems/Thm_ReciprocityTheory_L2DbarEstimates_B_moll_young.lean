-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_B_moll_young
-- name    : ReciprocityTheory.L2DbarEstimates.B.moll_young
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T13:29:49.36146+00:00
-- url     : https://prove2.me/theorems/7102ec38-9c66-4df1-8733-ccc441eb46de
-- title:
--   B: moll young
-- statement:
--   The B construction uses the moll young property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Mollifiers/MollEnormSqLe.lean#L105-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Mollifiers/MollEnormSqLe.lean#L105-L114

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Mollifiers_HasCompactSupport
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Mollifiers_MollEnormSqLe
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

theorem ReciprocityTheory.L2DbarEstimates.B.moll_young (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] : YoungSt E μ := by sorry
