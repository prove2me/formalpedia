-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_B_Kernel_eq_zero_of_le
-- name    : ReciprocityTheory.L2DbarEstimates.B.Kernel.eq_zero_of_le
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T14:29:58.746214+00:00
-- url     : https://prove2.me/theorems/2d8fe3f6-027f-4321-bd69-fb410e317896
-- title:
--   Kernel: eq zero of le
-- statement:
--   The Kernel construction uses the eq zero of le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Mollifiers/HasCompactSupport.lean#L17-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Mollifiers/HasCompactSupport.lean#L17-L21

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

theorem ReciprocityTheory.L2DbarEstimates.B.Kernel.eq_zero_of_le (K : Kernel E μ) {t : E} (ht : K.r ≤ ‖t‖) : K.toFun t = 0 := by sorry
