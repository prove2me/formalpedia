-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_continuous
-- name    : ReciprocityTheory.L2DbarEstimates.Ck.continuous
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:13:35.043861+00:00
-- url     : https://prove2.me/theorems/777ce3f8-6258-4d14-b926-313a517fbba0
-- title:
--   Ck: continuous
-- statement:
--   The Ck construction uses the continuous property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/ChartDerivatives/ChartSymmEventuallyEq.lean#L175-L184
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/ChartDerivatives/ChartSymmEventuallyEq.lean#L175-L184

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_HoloSmooth
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_ChartSymmEventuallyEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates
open Filter Topology Set
open scoped ContDiff
noncomputable section

theorem ReciprocityTheory.L2DbarEstimates.Ck.continuous {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (hz : IsLocalHomeomorph z) (k : ℕ) (f : M → ℂ) (hf : Ck n z k f) : Continuous f := by sorry
