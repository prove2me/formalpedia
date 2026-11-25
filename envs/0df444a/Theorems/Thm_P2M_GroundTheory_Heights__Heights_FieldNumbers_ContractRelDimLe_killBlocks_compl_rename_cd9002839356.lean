-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_ContractRelDimLe_killBlocks_compl_rename_cd9002839356
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_ContractRelDimLe_killBlocks_compl_rename_cd9002839356
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:17:04.366649+00:00
-- url     : https://prove2.me/theorems/04943f74-5924-4490-8905-7538da31b342
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers Contract Rel Dim Le kill Blocks compl rename cd9002839356: P2 M Ground Theory Heights  Heights Field Numbers Contract Rel Dim Le kill Blocks compl ren
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers Contract Rel Dim Le kill Blocks compl rename cd9002839356 construction uses the P2 M Ground Theory Heights  Heights Field Numbers Contract Rel Dim Le kill Blocks compl rename cd9002839356 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PContractRelDimLe.lean#L65-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PContractRelDimLe.lean#L65-L70

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

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_ContractRelDimLe_killBlocks_compl_rename_cd9002839356 :
    (killBlocks (ι := ι') (F := F) (Finset.univ.map j)ᶜ).comp (rename (blockIncl j ι')) =
      rename (blockIncl j ι') := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«ContractRelDimLe».«killBlocks_compl_rename» := P2M_GroundTheory_Heights__Heights_FieldNumbers_ContractRelDimLe_killBlocks_compl_rename_cd9002839356
