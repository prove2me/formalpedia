-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_contractPrime_bot_230ea120a67d
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_contractPrime_bot_230ea120a67d
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:32:02.461346+00:00
-- url     : https://prove2.me/theorems/f3c7e1c5-7dc1-44a3-8993-31f03f03a889
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers contract Prime bot 230ea120a67d: P2 M Ground Theory Heights  Heights Field Numbers contract Prime bot 230ea120a67d
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers contract Prime bot 230ea120a67d construction uses the P2 M Ground Theory Heights  Heights Field Numbers contract Prime bot 230ea120a67d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/StatementsExamples.lean#L130-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/StatementsExamples.lean#L130-L132

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

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_contractPrime_bot_230ea120a67d {K K' : Type*} {F : Type*} [Field F] (j : K ↪ K') (ι' : K' → Type*) :
    contractPrime j (⊥ : Ideal (MRing ι' F)) = ⊥ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«contractPrime_bot» := P2M_GroundTheory_Heights__Heights_FieldNumbers_contractPrime_bot_230ea120a67d
