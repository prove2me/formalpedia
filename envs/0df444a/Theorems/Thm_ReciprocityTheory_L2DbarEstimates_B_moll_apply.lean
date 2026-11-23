-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_B_moll_apply
-- name    : ReciprocityTheory.L2DbarEstimates.B.moll_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:29:56.081198+00:00
-- url     : https://prove2.me/theorems/23044e96-5411-4891-8d84-9b32953586d8
-- title:
--   B: moll apply
-- statement:
--   The B construction uses the moll apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Mollifiers/HasCompactSupport.lean#L23-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Mollifiers/HasCompactSupport.lean#L23-L24

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
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {μ : Measure E}

theorem ReciprocityTheory.L2DbarEstimates.B.moll_apply (K : Kernel E μ) (u : E → ℂ) (x : E) :
    moll K u x = ∫ t, K.toFun t • u (x - t) ∂μ := by sorry
