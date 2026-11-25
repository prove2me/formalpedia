-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_KThetaCubeParseval_torusChar_mul_conj_7974dddcddd1
-- name    : P2M_GroundTheory_Heights__Heights_KThetaCubeParseval_torusChar_mul_conj_7974dddcddd1
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:26:58.202313+00:00
-- url     : https://prove2.me/theorems/9f7357be-9922-436c-b94d-c46a87547208
-- title:
--   P2 M Ground Theory Heights  Heights KTheta Cube Parseval torus Char mul conj 7974dddcddd1: P2 M Ground Theory Heights  Heights KTheta Cube Parseval torus Char mul conj 7974dddcddd1
-- statement:
--   The P2 M Ground Theory Heights  Heights KTheta Cube Parseval torus Char mul conj 7974dddcddd1 construction uses the P2 M Ground Theory Heights  Heights KTheta Cube Parseval torus Char mul conj 7974dddcddd1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PThetaCubeParseval.lean#L23-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PThetaCubeParseval.lean#L23-L30

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsTheta
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PThetaCubeParseval
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MeasureTheory Real ComplexConjugate
noncomputable section
open GroundTheory.Heights₂.Heights.KThetaCubeParseval

theorem P2M_GroundTheory_Heights__Heights_KThetaCubeParseval_torusChar_mul_conj_7974dddcddd1 {g : ℕ} (k l : Fin g → ℤ) (u : Fin g → ℝ) :
    torusChar k u * conj (torusChar l u) = torusChar (k - l) u := by sorry

alias «GroundTheory».«Heights₂».«Heights».«KThetaCubeParseval».«torusChar_mul_conj» := P2M_GroundTheory_Heights__Heights_KThetaCubeParseval_torusChar_mul_conj_7974dddcddd1
