-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_intNum_projectiveSpace_3fbe2c0ead0a
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_intNum_projectiveSpace_3fbe2c0ead0a
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T13:12:14.868703+00:00
-- url     : https://prove2.me/theorems/c7ae9b1d-016e-51ad-95de-06e44e73fca4
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers int Num projective Space 3fbe2c0ead0a: P2 M Ground Theory Heights  Heights Field Numbers int Num projective Space 3fbe2c0ead0a
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers int Num projective Space 3fbe2c0ead0a construction uses the P2 M Ground Theory Heights  Heights Field Numbers int Num projective Space 3fbe2c0ead0a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/StatementsExamples.lean#L105-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/StatementsExamples.lean#L105-L120

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

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_intNum_projectiveSpace_3fbe2c0ead0a (F : Type*) [Field F] (N : ℕ) :
    intNum F (⊥ : Ideal (MRing (ProjIdx N) F)) (fun _ : Fin N => (1 : Unit → ℤ)) = 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«intNum_projectiveSpace» := P2M_GroundTheory_Heights__Heights_FieldNumbers_intNum_projectiveSpace_3fbe2c0ead0a
