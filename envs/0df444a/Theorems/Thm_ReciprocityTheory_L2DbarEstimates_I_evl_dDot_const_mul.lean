-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_evl_dDot_const_mul
-- name    : ReciprocityTheory.L2DbarEstimates.I.evl_dDot_const_mul
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T10:57:48.128643+00:00
-- url     : https://prove2.me/theorems/beef00c2-fb08-4b8b-932e-02f046500414
-- title:
--   I: evl d Dot const mul
-- statement:
--   The I construction uses the evl d Dot const mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/EvLeviA.lean#L17-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/EvLeviA.lean#L17-L22

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_BergmanExistsStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_EvLeviA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.I
open scoped ComplexConjugate ContDiff
noncomputable section

theorem ReciprocityTheory.L2DbarEstimates.I.evl_dDot_const_mul {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (c : ℂ)
    (f : M → ℂ) (hf : Ck n z 1 f) (x : M) (ξ : Fin n → ℂ) :
    dDot n z (fun y => c * f y) x ξ = c * dDot n z f x ξ := by sorry
