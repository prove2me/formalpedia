-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_exists_form_one_413d684437fd
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_exists_form_one_413d684437fd
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:17:51.034078+00:00
-- url     : https://prove2.me/theorems/eff7ba05-7b2f-50da-bfa5-28f273b08b0b
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers exists form one 413d684437fd: P2 M Ground Theory Heights  Heights Field Numbers exists form one 413d684437fd
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers exists form one 413d684437fd construction uses the P2 M Ground Theory Heights  Heights Field Numbers exists form one 413d684437fd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PIntNumBaseChange.lean#L88-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PIntNumBaseChange.lean#L88-L94

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PGradedFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PIntNumBaseChange
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
variable {σ : Type*} {F : Type*} [Field F] {F' : Type*} [Field F'] [Algebra F F']

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_exists_form_one_413d684437fd : ∃ φ : F' →ₗ[F] F, φ 1 = 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«exists_form_one» := P2M_GroundTheory_Heights__Heights_FieldNumbers_exists_form_one_413d684437fd
