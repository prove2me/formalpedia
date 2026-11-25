-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_FlagEq_antisym_psumAt_mul_adaccf6e47a0
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_FlagEq_antisym_psumAt_mul_adaccf6e47a0
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T04:19:32.546801+00:00
-- url     : https://prove2.me/theorems/ae6337fc-6340-4357-8234-7c8c9e2d05b9
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Flag Eq antisym psum At mul adaccf6e47a0: P2 M Ground Theory Heights  Heights Rest Terms Flag Eq antisym psum At mul adaccf6e47a0
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Flag Eq antisym psum At mul adaccf6e47a0 construction uses the P2 M Ground Theory Heights  Heights Rest Terms Flag Eq antisym psum At mul adaccf6e47a0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/FlagIntegralRealEqMulDdConst.lean#L67-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/FlagIntegralRealEqMulDdConst.lean#L67-L70

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_CoeffRenameProdCongrRight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_FlagIntegralRealEqMulDdConst
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.RestTerms
open MvPolynomial Finset
noncomputable section
open GroundTheory.Heights₂.Heights.RestTerms.FlagEq

theorem P2M_GroundTheory_Heights__Heights_RestTerms_FlagEq_antisym_psumAt_mul_adaccf6e47a0 (f j k m : ℕ) (τ : Fin f) (G : IndefiniteRowSideFullHecke.RestTerms.Roots f j k) :
    antisym f j k (IndefiniteRowSideFullHecke.RestTerms.psumAt f j k m τ * G) =
      IndefiniteRowSideFullHecke.RestTerms.psumAt f j k m τ * antisym f j k G := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«FlagEq».«antisym_psumAt_mul» := P2M_GroundTheory_Heights__Heights_RestTerms_FlagEq_antisym_psumAt_mul_adaccf6e47a0
