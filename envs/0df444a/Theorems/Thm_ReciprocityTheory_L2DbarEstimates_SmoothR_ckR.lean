-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_ckR
-- name    : ReciprocityTheory.L2DbarEstimates.SmoothR.ckR
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:27:49.959802+00:00
-- url     : https://prove2.me/theorems/60f856a5-3175-4218-9323-40a3aaf70252
-- title:
--   Smooth R: ck R
-- statement:
--   The Smooth R construction uses the ck R property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/ChartDerivatives/ChartSymmEventuallyEq.lean#L165-L168
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/ChartDerivatives/ChartSymmEventuallyEq.lean#L165-L168

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

theorem ReciprocityTheory.L2DbarEstimates.SmoothR.ckR {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (k : ℕ) (f : M → ℝ)
    (hf : SmoothR n z f) : CkR n z k f := by sorry
