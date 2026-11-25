-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_coeffForm_map_mul_140b383ad26d
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_coeffForm_map_mul_140b383ad26d
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:17:18.828822+00:00
-- url     : https://prove2.me/theorems/df18efa2-6bc9-4480-b5fe-86877e2d1ccb
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers coeff Form map mul 140b383ad26d: P2 M Ground Theory Heights  Heights Field Numbers coeff Form map mul 140b383ad26d
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers coeff Form map mul 140b383ad26d construction uses the P2 M Ground Theory Heights  Heights Field Numbers coeff Form map mul 140b383ad26d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PIntNumBaseChange.lean#L48-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PIntNumBaseChange.lean#L48-L52

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

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_coeffForm_map_mul_140b383ad26d (φ : F' →ₗ[F] F) (g : MvPolynomial σ F) (f : MvPolynomial σ F') :
    coeffForm φ (map (algebraMap F F') g * f) = g * coeffForm φ f := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«coeffForm_map_mul» := P2M_GroundTheory_Heights__Heights_FieldNumbers_coeffForm_map_mul_140b383ad26d
