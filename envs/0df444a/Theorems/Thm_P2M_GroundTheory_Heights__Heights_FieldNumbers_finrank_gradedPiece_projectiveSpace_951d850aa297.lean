-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_finrank_gradedPiece_projectiveSpace_951d850aa297
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_finrank_gradedPiece_projectiveSpace_951d850aa297
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:17:17.094587+00:00
-- url     : https://prove2.me/theorems/5a6af7ff-cc2a-4805-b109-8248d512aa1e
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers finrank graded Piece projective Space 951d850aa297: P2 M Ground Theory Heights  Heights Field Numbers finrank graded Piece projective Space 951d850aa2
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers finrank graded Piece projective Space 951d850aa297 construction uses the P2 M Ground Theory Heights  Heights Field Numbers finrank graded Piece projective Space 951d850aa297 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/StatementsExamples.lean#L55-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/StatementsExamples.lean#L55-L83

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsExamples
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_finrank_gradedPiece_projectiveSpace_951d850aa297 (F : Type*) [Field F] (N a : ℕ) :
    Module.finrank F (gradedPiece (⊥ : Ideal (MRing (ProjIdx N) F)) (fun _ => a)) =
      (a + N).choose N := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«finrank_gradedPiece_projectiveSpace» := P2M_GroundTheory_Heights__Heights_FieldNumbers_finrank_gradedPiece_projectiveSpace_951d850aa297
