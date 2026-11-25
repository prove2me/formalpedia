-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_ContractRelDimLe_ringKrullDim_contract_eq_killIdeal_facff24de20d
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_ContractRelDimLe_ringKrullDim_contract_eq_killIdeal_facff24de20d
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:17:01.326003+00:00
-- url     : https://prove2.me/theorems/81702df1-6625-4fc0-a1b6-bc3b4176109d
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers Contract Rel Dim Le ring Krull Dim contract eq kill Ideal facff24de20d: P2 M Ground Theory Heights  Heights Field Numbers Contract Rel Dim Le ring Kru
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers Contract Rel Dim Le ring Krull Dim contract eq kill Ideal facff24de20d construction uses the P2 M Ground Theory Heights  Heights Field Numbers Contract Rel Dim Le ring Krull Dim contract eq kill Ideal facff24de20d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PContractRelDimLe.lean#L94-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PContractRelDimLe.lean#L94-L116

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsContractRelDimLe
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPFContracted
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PContractRelDimLe
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
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR PFContracted
noncomputable section
universe u
open GroundTheory.Heights₂.Heights.FieldNumbers.ContractRelDimLe
variable {K K' : Type*} [Fintype K] [DecidableEq K] [Fintype K'] [DecidableEq K'] {F : Type*}
  [Field F] (j : K ↪ K') (ι' : K' → Type*)

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_ContractRelDimLe_ringKrullDim_contract_eq_killIdeal_facff24de20d (P' : Ideal (MRing ι' F)) :
    ringKrullDim (MRing (fun k => ι' (j k)) F ⧸ contractPrime j P') =
      ringKrullDim (MRing ι' F ⧸ killIdeal P' (Finset.univ.map j)ᶜ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«ContractRelDimLe».«ringKrullDim_contract_eq_killIdeal» := P2M_GroundTheory_Heights__Heights_FieldNumbers_ContractRelDimLe_ringKrullDim_contract_eq_killIdeal_facff24de20d
