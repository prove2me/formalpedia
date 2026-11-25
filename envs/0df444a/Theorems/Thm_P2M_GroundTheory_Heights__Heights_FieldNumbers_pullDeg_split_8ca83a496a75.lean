-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_pullDeg_split_8ca83a496a75
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_pullDeg_split_8ca83a496a75
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:18:59.233537+00:00
-- url     : https://prove2.me/theorems/1359ae4d-8d50-5197-92f4-b33061fc3476
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers pull Deg split 8ca83a496a75: P2 M Ground Theory Heights  Heights Field Numbers pull Deg split 8ca83a496a75
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers pull Deg split 8ca83a496a75 construction uses the P2 M Ground Theory Heights  Heights Field Numbers pull Deg split 8ca83a496a75 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/ContractBlocksSplitPrime.lean#L82-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/ContractBlocksSplitPrime.lean#L82-L91

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

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_pullDeg_split_8ca83a496a75 (b : K → ℤ) :
    IndefiniteRowSideFullHecke.FieldNumbers.pullDeg (L := blockCompl j) b ∘ (splitBlockEquiv j).symm = pullDeg j b := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«pullDeg_split» := P2M_GroundTheory_Heights__Heights_FieldNumbers_pullDeg_split_8ca83a496a75
