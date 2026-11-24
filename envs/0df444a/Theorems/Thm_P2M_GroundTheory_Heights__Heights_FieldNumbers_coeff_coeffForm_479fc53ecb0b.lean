-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_coeff_coeffForm_479fc53ecb0b
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_coeff_coeffForm_479fc53ecb0b
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:30:25.514261+00:00
-- url     : https://prove2.me/theorems/a41d096b-b652-4d14-861e-1add15fb31b4
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers coeff coeff Form 479fc53ecb0b: P2 M Ground Theory Heights  Heights Field Numbers coeff coeff Form 479fc53ecb0b
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers coeff coeff Form 479fc53ecb0b construction uses the P2 M Ground Theory Heights  Heights Field Numbers coeff coeff Form 479fc53ecb0b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PIntNumBaseChange.lean#L33-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PIntNumBaseChange.lean#L33-L35

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

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_coeff_coeffForm_479fc53ecb0b (φ : F' →ₗ[F] F) (f : MvPolynomial σ F') (ν : σ →₀ ℕ) :
    coeff ν (coeffForm φ f) = φ (coeff ν f) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«coeff_coeffForm» := P2M_GroundTheory_Heights__Heights_FieldNumbers_coeff_coeffForm_479fc53ecb0b
