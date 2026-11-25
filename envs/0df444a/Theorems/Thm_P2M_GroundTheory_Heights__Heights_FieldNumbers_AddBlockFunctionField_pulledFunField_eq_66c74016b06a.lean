-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_AddBlockFunctionField_pulledFunField_eq_66c74016b06a
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_AddBlockFunctionField_pulledFunField_eq_66c74016b06a
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:17:03.047151+00:00
-- url     : https://prove2.me/theorems/896d2bd7-3fc2-56db-b0ff-c4fb9c5cae97
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers Add Block Function Field pulled Fun Field eq 66c74016b06a: P2 M Ground Theory Heights  Heights Field Numbers Add Block Function Field pulled Fun Field
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers Add Block Function Field pulled Fun Field eq 66c74016b06a construction uses the P2 M Ground Theory Heights  Heights Field Numbers Add Block Function Field pulled Fun Field eq 66c74016b06a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/AddBlockVarEquivFst.lean#L34-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/AddBlockVarEquivFst.lean#L34-L50

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PfContractedHypothesesExample
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_AddBlockVarEquivFst
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
open GroundTheory.Heights₂.Heights.FieldNumbers.AddBlockFunctionField
variable {F : Type u} [Field F] {K L : Type} {ι : K → Type} {ι₂ : L → Type}

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_AddBlockFunctionField_pulledFunField_eq_66c74016b06a [DecidableEq K] (P' : Ideal (MRing (Sum.elim ι ι₂) F)) [P'.IsPrime] :
    IndefiniteRowSideFullHecke.FieldNumbers.pulledFunField ι₂ P' =
      (homFracDegZero (contractPrime (Function.Embedding.inl : K ↪ K ⊕ L) P')).map
        (contractFracMap Function.Embedding.inl P') := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«AddBlockFunctionField».«pulledFunField_eq» := P2M_GroundTheory_Heights__Heights_FieldNumbers_AddBlockFunctionField_pulledFunField_eq_66c74016b06a
