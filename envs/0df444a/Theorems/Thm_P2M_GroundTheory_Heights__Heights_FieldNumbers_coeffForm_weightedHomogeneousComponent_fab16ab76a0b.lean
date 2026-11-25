-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_coeffForm_weightedHomogeneousComponent_fab16ab76a0b
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_coeffForm_weightedHomogeneousComponent_fab16ab76a0b
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:17:06.273487+00:00
-- url     : https://prove2.me/theorems/65321684-8d86-47ee-9405-c7b12b40150a
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers coeff Form weighted Homogeneous Component fab16ab76a0b: P2 M Ground Theory Heights  Heights Field Numbers coeff Form weighted Homogeneous Component fa
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers coeff Form weighted Homogeneous Component fab16ab76a0b construction uses the P2 M Ground Theory Heights  Heights Field Numbers coeff Form weighted Homogeneous Component fab16ab76a0b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PIntNumBaseChange.lean#L59-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PIntNumBaseChange.lean#L59-L66

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

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_coeffForm_weightedHomogeneousComponent_fab16ab76a0b {M : Type*} [AddCommMonoid M] (φ : F' →ₗ[F] F)
    (w : σ → M) (n : M) (f : MvPolynomial σ F') :
    coeffForm φ (weightedHomogeneousComponent w n f) =
      weightedHomogeneousComponent w n (coeffForm φ f) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«coeffForm_weightedHomogeneousComponent» := P2M_GroundTheory_Heights__Heights_FieldNumbers_coeffForm_weightedHomogeneousComponent_fab16ab76a0b
