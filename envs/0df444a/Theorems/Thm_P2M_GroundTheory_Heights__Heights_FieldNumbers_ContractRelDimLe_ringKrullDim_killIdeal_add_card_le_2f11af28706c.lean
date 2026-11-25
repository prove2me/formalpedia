-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_ContractRelDimLe_ringKrullDim_killIdeal_add_card_le_2f11af28706c
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_ContractRelDimLe_ringKrullDim_killIdeal_add_card_le_2f11af28706c
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:17:18.886316+00:00
-- url     : https://prove2.me/theorems/2399c467-f9a1-4f3d-9728-5ffa96975fbb
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers Contract Rel Dim Le ring Krull Dim kill Ideal add card le 2f11af28706c: P2 M Ground Theory Heights  Heights Field Numbers Contract Rel Dim Le ring Kru
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers Contract Rel Dim Le ring Krull Dim kill Ideal add card le 2f11af28706c construction uses the P2 M Ground Theory Heights  Heights Field Numbers Contract Rel Dim Le ring Krull Dim kill Ideal add card le 2f11af28706c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PContractRelDimLe.lean#L20-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PContractRelDimLe.lean#L20-L54

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
variable {K : Type*} [DecidableEq K] {ι : K → Type*} {F : Type*} [Field F]

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_ContractRelDimLe_ringKrullDim_killIdeal_add_card_le_2f11af28706c {Q : Ideal (MRing ι F)} [Q.IsPrime]
    (hQ : ∀ (T : Finset K) (q : MRing ι F), q ∈ Q → killBlocks T q ∈ Q) (hrel : IsRelevant Q)
    (T : Finset K) :
    ringKrullDim (MRing ι F ⧸ killIdeal Q T) + (T.card : WithBot ℕ∞) ≤
      ringKrullDim (MRing ι F ⧸ Q) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«ContractRelDimLe».«ringKrullDim_killIdeal_add_card_le» := P2M_GroundTheory_Heights__Heights_FieldNumbers_ContractRelDimLe_ringKrullDim_killIdeal_add_card_le_2f11af28706c
