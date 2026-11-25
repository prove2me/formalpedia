-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_contractBlocks_splitPrime_59970ed6b43c
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_contractBlocks_splitPrime_59970ed6b43c
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:18:41.461677+00:00
-- url     : https://prove2.me/theorems/8c137226-09f1-4ed4-b8a3-560b0bd26f40
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers contract Blocks split Prime 59970ed6b43c: P2 M Ground Theory Heights  Heights Field Numbers contract Blocks split Prime 59970ed6b43c
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers contract Blocks split Prime 59970ed6b43c construction uses the P2 M Ground Theory Heights  Heights Field Numbers contract Blocks split Prime 59970ed6b43c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/ContractBlocksSplitPrime.lean#L70-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/ContractBlocksSplitPrime.lean#L70-L80

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

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_contractBlocks_splitPrime_59970ed6b43c {F : Type u} [Field F] (P' : Ideal (MRing ι' F)) :
    IndefiniteRowSideFullHecke.FieldNumbers.contractBlocks (fun l : blockCompl j => ι' l.1) (splitPrime j P') =
      contractPrime j P' := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«contractBlocks_splitPrime» := P2M_GroundTheory_Heights__Heights_FieldNumbers_contractBlocks_splitPrime_59970ed6b43c
