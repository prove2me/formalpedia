-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_addBlockPrime_bot_7e03f9ed558c
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_addBlockPrime_bot_7e03f9ed558c
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T13:12:14.908499+00:00
-- url     : https://prove2.me/theorems/2be5d228-6da8-4ee8-9d92-5a7f9c616855
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers add Block Prime bot 7e03f9ed558c: P2 M Ground Theory Heights  Heights Field Numbers add Block Prime bot 7e03f9ed558c
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers add Block Prime bot 7e03f9ed558c construction uses the P2 M Ground Theory Heights  Heights Field Numbers add Block Prime bot 7e03f9ed558c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/StatementsExamples.lean#L134-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/StatementsExamples.lean#L134-L136

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsExamples
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

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_addBlockPrime_bot_7e03f9ed558c {K : Type*} {F : Type*} [Field F] (ι : K → Type) (N : ℕ) :
    addBlockPrime N (⊥ : Ideal (MRing ι F)) = ⊥ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«addBlockPrime_bot» := P2M_GroundTheory_Heights__Heights_FieldNumbers_addBlockPrime_bot_7e03f9ed558c
