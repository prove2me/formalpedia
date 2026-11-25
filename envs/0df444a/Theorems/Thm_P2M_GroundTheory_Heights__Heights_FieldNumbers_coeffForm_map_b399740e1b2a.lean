-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_coeffForm_map_b399740e1b2a
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_coeffForm_map_b399740e1b2a
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:17:07.559179+00:00
-- url     : https://prove2.me/theorems/db10c786-112d-499c-b121-993a378b9835
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers coeff Form map b399740e1b2a: P2 M Ground Theory Heights  Heights Field Numbers coeff Form map b399740e1b2a
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers coeff Form map b399740e1b2a construction uses the P2 M Ground Theory Heights  Heights Field Numbers coeff Form map b399740e1b2a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PIntNumBaseChange.lean#L54-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PIntNumBaseChange.lean#L54-L57

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

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_coeffForm_map_b399740e1b2a (φ : F' →ₗ[F] F) (hφ : φ 1 = 1) (g : MvPolynomial σ F) :
    coeffForm φ (map (algebraMap F F') g) = g := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«coeffForm_map» := P2M_GroundTheory_Heights__Heights_FieldNumbers_coeffForm_map_b399740e1b2a
