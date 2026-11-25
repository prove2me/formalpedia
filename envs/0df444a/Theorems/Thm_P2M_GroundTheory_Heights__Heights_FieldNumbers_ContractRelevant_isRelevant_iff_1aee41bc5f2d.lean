-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_ContractRelevant_isRelevant_iff_1aee41bc5f2d
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_ContractRelevant_isRelevant_iff_1aee41bc5f2d
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:16:54.34323+00:00
-- url     : https://prove2.me/theorems/5d3885c3-7eba-4a94-ae04-c5273d0e4ffb
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers Contract Relevant is Relevant iff 1aee41bc5f2d: P2 M Ground Theory Heights  Heights Field Numbers Contract Relevant is Relevant iff 1aee41bc5f2d
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers Contract Relevant is Relevant iff 1aee41bc5f2d construction uses the P2 M Ground Theory Heights  Heights Field Numbers Contract Relevant is Relevant iff 1aee41bc5f2d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/ContractRelevant.lean#L11-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/ContractRelevant.lean#L11-L21

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_ContractRelevant
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers GroundTheory.Heights₂.Heights.FieldNumbers.ContractRelevant
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_ContractRelevant_isRelevant_iff_1aee41bc5f2d {R : Type*} [CommRing R] {K : Type*} {ι : K → Type*}
    (I : Ideal (MRing ι R)) :
    IsRelevant I ↔ ∀ k, ∃ v : Σ k, ι k, v.1 = k ∧ (X v : MRing ι R) ∉ I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«ContractRelevant».«isRelevant_iff» := P2M_GroundTheory_Heights__Heights_FieldNumbers_ContractRelevant_isRelevant_iff_1aee41bc5f2d
