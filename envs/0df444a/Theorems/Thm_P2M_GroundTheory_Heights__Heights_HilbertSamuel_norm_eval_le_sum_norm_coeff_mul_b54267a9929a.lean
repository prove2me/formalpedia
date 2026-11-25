-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_norm_eval_le_sum_norm_coeff_mul_b54267a9929a
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_norm_eval_le_sum_norm_coeff_mul_b54267a9929a
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:19:15.290407+00:00
-- url     : https://prove2.me/theorems/b6d31c12-53d3-5f7b-9b19-009175d6c1f4
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel norm eval le sum norm coeff mul b54267a9929a: P2 M Ground Theory Heights  Heights Hilbert Samuel norm eval le sum norm coeff mul b54267a9929a
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel norm eval le sum norm coeff mul b54267a9929a construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel norm eval le sum norm coeff mul b54267a9929a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/IrreducibleConnected/PMonicRootGrowth.lean#L9-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/IrreducibleConnected/PMonicRootGrowth.lean#L9-L23

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_IrreducibleConnected_StMonicRootGrowth
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_IrreducibleConnected_PMonicRootGrowth
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial Finset

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_norm_eval_le_sum_norm_coeff_mul_b54267a9929a {d : ℕ} (a : MvPolynomial (Fin d) ℂ) (y : Fin d → ℂ) :
    ‖eval y a‖ ≤ (∑ s ∈ a.support, ‖coeff s a‖) * (1 + ‖y‖) ^ a.totalDegree := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«norm_eval_le_sum_norm_coeff_mul» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_norm_eval_le_sum_norm_coeff_mul_b54267a9929a
