-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_B_Kernel_hasCompactSupport
-- name    : ReciprocityTheory.L2DbarEstimates.B.Kernel.hasCompactSupport
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:29:57.731433+00:00
-- url     : https://prove2.me/theorems/299d8453-2e6b-4395-922e-98f3af68609c
-- title:
--   Kernel: has Compact Support
-- statement:
--   The Kernel construction uses the has Compact Support property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Mollifiers/HasCompactSupport.lean#L12-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Mollifiers/HasCompactSupport.lean#L12-L15

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

theorem ReciprocityTheory.L2DbarEstimates.B.Kernel.hasCompactSupport (K : Kernel E μ) : HasCompactSupport K.toFun := by sorry
