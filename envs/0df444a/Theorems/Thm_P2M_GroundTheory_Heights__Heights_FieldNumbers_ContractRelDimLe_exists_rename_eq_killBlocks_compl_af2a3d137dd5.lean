-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_ContractRelDimLe_exists_rename_eq_killBlocks_compl_af2a3d137dd5
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_ContractRelDimLe_exists_rename_eq_killBlocks_compl_af2a3d137dd5
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:16:44.316695+00:00
-- url     : https://prove2.me/theorems/82a7005d-c9ba-5a33-8241-260c07ad6605
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers Contract Rel Dim Le exists rename eq kill Blocks compl af2a3d137dd5: P2 M Ground Theory Heights  Heights Field Numbers Contract Rel Dim Le exists rena
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers Contract Rel Dim Le exists rename eq kill Blocks compl af2a3d137dd5 construction uses the P2 M Ground Theory Heights  Heights Field Numbers Contract Rel Dim Le exists rename eq kill Blocks compl af2a3d137dd5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PContractRelDimLe.lean#L74-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PContractRelDimLe.lean#L74-L92

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
omit [DecidableEq K]

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_ContractRelDimLe_exists_rename_eq_killBlocks_compl_af2a3d137dd5 (x : MRing ι' F) :
    ∃ a : MRing (fun k => ι' (j k)) F,
      rename (blockIncl j ι') a = killBlocks (Finset.univ.map j)ᶜ x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«ContractRelDimLe».«exists_rename_eq_killBlocks_compl» := P2M_GroundTheory_Heights__Heights_FieldNumbers_ContractRelDimLe_exists_rename_eq_killBlocks_compl_af2a3d137dd5
