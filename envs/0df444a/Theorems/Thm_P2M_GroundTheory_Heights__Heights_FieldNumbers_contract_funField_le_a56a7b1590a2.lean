-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_contract_funField_le_a56a7b1590a2
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_contract_funField_le_a56a7b1590a2
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:17:45.332809+00:00
-- url     : https://prove2.me/theorems/82df786f-c353-40d1-898c-1d939a723d97
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers contract fun Field le a56a7b1590a2: P2 M Ground Theory Heights  Heights Field Numbers contract fun Field le a56a7b1590a2
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers contract fun Field le a56a7b1590a2 construction uses the P2 M Ground Theory Heights  Heights Field Numbers contract fun Field le a56a7b1590a2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/ContractBlocksSplitPrime.lean#L103-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/ContractBlocksSplitPrime.lean#L103-L114

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PfContractedHypothesesExample
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_HomFracDegZeroEqFunField
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_AddBlockVarEquivFst
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsRename
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_ContractBlocksSplitPrime
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

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_contract_funField_le_a56a7b1590a2 (h₁ : RenameMultiHomog.Statement.{u}) {F : Type u} [Field F]
    {K K' : Type} [DecidableEq K] [DecidableEq K'] (j : K ↪ K') {ι' : K' → Type}
    (P' : Ideal (MRing ι' F)) [P'.IsPrime] :
    (homFracDegZero (contractPrime j P')).map (contractFracMap j P') ≤ homFracDegZero P' := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«contract_funField_le» := P2M_GroundTheory_Heights__Heights_FieldNumbers_contract_funField_le_a56a7b1590a2
