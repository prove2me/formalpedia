-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_relDim_splitPrime_1aec8e01fe69
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_relDim_splitPrime_1aec8e01fe69
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:19:11.520633+00:00
-- url     : https://prove2.me/theorems/98cc37a1-3e61-572f-8e68-7492c83286a8
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers rel Dim split Prime 1aec8e01fe69: P2 M Ground Theory Heights  Heights Field Numbers rel Dim split Prime 1aec8e01fe69
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers rel Dim split Prime 1aec8e01fe69 construction uses the P2 M Ground Theory Heights  Heights Field Numbers rel Dim split Prime 1aec8e01fe69 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/ContractBlocksSplitPrime.lean#L93-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/ContractBlocksSplitPrime.lean#L93-L99

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
variable {K K' : Type} (j : K ↪ K') (ι' : K' → Type)

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_relDim_splitPrime_1aec8e01fe69 {F : Type u} [Field F] [Fintype K] [Fintype K'] [Fintype (blockCompl j)]
    (P' : Ideal (MRing ι' F)) : relDim (splitPrime j P') = relDim P' := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«relDim_splitPrime» := P2M_GroundTheory_Heights__Heights_FieldNumbers_relDim_splitPrime_1aec8e01fe69
