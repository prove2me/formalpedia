-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_B_Kernel_lintegral_ofReal
-- name    : ReciprocityTheory.L2DbarEstimates.B.Kernel.lintegral_ofReal
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T13:29:41.696966+00:00
-- url     : https://prove2.me/theorems/36f5fdb0-16c4-4e28-a026-1e6266e1b896
-- title:
--   Kernel: lintegral of Real
-- statement:
--   The Kernel construction uses the lintegral of Real property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Mollifiers/MollEnormSqLe.lean#L8-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Mollifiers/MollEnormSqLe.lean#L8-L14

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

theorem ReciprocityTheory.L2DbarEstimates.B.Kernel.lintegral_ofReal (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] (K : Kernel E μ) :
    ∫⁻ t, ENNReal.ofReal (K.toFun t) ∂μ = 1 := by sorry
