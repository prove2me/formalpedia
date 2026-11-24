-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_form_algebraMap_mul_519b69638a62
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_form_algebraMap_mul_519b69638a62
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:02:12.649409+00:00
-- url     : https://prove2.me/theorems/4b576fad-fcb3-45b0-838f-980ecc3ff65b
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers form algebra Map mul 519b69638a62: P2 M Ground Theory Heights  Heights Field Numbers form algebra Map mul 519b69638a62
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers form algebra Map mul 519b69638a62 construction uses the P2 M Ground Theory Heights  Heights Field Numbers form algebra Map mul 519b69638a62 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PIntNumBaseChange.lean#L44-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PIntNumBaseChange.lean#L44-L46

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

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_form_algebraMap_mul_519b69638a62 (φ : F' →ₗ[F] F) (a : F) (x : F') :
    φ (algebraMap F F' a * x) = a * φ x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«form_algebraMap_mul» := P2M_GroundTheory_Heights__Heights_FieldNumbers_form_algebraMap_mul_519b69638a62
