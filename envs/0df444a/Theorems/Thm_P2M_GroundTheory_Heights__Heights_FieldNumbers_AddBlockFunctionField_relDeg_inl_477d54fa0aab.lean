-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_AddBlockFunctionField_relDeg_inl_477d54fa0aab
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_AddBlockFunctionField_relDeg_inl_477d54fa0aab
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:59:29.281855+00:00
-- url     : https://prove2.me/theorems/d1d91bde-6b68-4adf-9501-afcc02d72c18
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers Add Block Function Field rel Deg inl 477d54fa0aab: P2 M Ground Theory Heights  Heights Field Numbers Add Block Function Field rel Deg inl 477d54fa0aab
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers Add Block Function Field rel Deg inl 477d54fa0aab construction uses the P2 M Ground Theory Heights  Heights Field Numbers Add Block Function Field rel Deg inl 477d54fa0aab property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/AddBlockVarEquivFst.lean#L52-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/AddBlockVarEquivFst.lean#L52-L57

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

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_AddBlockFunctionField_relDeg_inl_477d54fa0aab [DecidableEq K] [DecidableEq L] (P' : Ideal (MRing (Sum.elim ι ι₂) F))
    [P'.IsPrime] :
    relDeg (Function.Embedding.inl : K ↪ K ⊕ L) P' = IndefiniteRowSideFullHecke.FieldNumbers.fibreDeg ι₂ P' := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«AddBlockFunctionField».«relDeg_inl» := P2M_GroundTheory_Heights__Heights_FieldNumbers_AddBlockFunctionField_relDeg_inl_477d54fa0aab
