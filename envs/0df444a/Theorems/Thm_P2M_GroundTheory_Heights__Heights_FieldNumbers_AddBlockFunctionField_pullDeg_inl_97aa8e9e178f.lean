-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_AddBlockFunctionField_pullDeg_inl_97aa8e9e178f
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_AddBlockFunctionField_pullDeg_inl_97aa8e9e178f
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:16:56.762251+00:00
-- url     : https://prove2.me/theorems/064c999b-725a-50ca-862f-71f4447aaffa
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers Add Block Function Field pull Deg inl 97aa8e9e178f: P2 M Ground Theory Heights  Heights Field Numbers Add Block Function Field pull Deg inl 97aa8e9e17
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers Add Block Function Field pull Deg inl 97aa8e9e178f construction uses the P2 M Ground Theory Heights  Heights Field Numbers Add Block Function Field pull Deg inl 97aa8e9e178f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/AddBlockVarEquivFst.lean#L23-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/AddBlockVarEquivFst.lean#L23-L32

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

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_AddBlockFunctionField_pullDeg_inl_97aa8e9e178f (b : K → ℤ) :
    pullDeg (Function.Embedding.inl : K ↪ K ⊕ L) b = IndefiniteRowSideFullHecke.FieldNumbers.pullDeg (L := L) b := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«AddBlockFunctionField».«pullDeg_inl» := P2M_GroundTheory_Heights__Heights_FieldNumbers_AddBlockFunctionField_pullDeg_inl_97aa8e9e178f
