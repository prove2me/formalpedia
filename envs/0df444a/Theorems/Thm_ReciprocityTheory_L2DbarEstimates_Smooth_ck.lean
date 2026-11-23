-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_ck
-- name    : ReciprocityTheory.L2DbarEstimates.Smooth.ck
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:20:22.646506+00:00
-- url     : https://prove2.me/theorems/cbe49bd7-3521-46d2-9107-e964f46d151b
-- title:
--   Smooth: ck
-- statement:
--   The Smooth construction uses the ck property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/ChartDerivatives/ChartSymmEventuallyEq.lean#L160-L163
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/ChartDerivatives/ChartSymmEventuallyEq.lean#L160-L163

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

theorem ReciprocityTheory.L2DbarEstimates.Smooth.ck {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (k : ℕ) (f : M → ℂ)
    (hf : Smooth n z f) : Ck n z k f := by sorry
