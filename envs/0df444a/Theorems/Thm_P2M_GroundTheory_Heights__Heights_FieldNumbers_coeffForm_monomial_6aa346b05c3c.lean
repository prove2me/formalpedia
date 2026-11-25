-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_coeffForm_monomial_6aa346b05c3c
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_coeffForm_monomial_6aa346b05c3c
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:17:25.696444+00:00
-- url     : https://prove2.me/theorems/631f7c81-f76f-4641-be01-380390e88d6e
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers coeff Form monomial 6aa346b05c3c: P2 M Ground Theory Heights  Heights Field Numbers coeff Form monomial 6aa346b05c3c
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers coeff Form monomial 6aa346b05c3c construction uses the P2 M Ground Theory Heights  Heights Field Numbers coeff Form monomial 6aa346b05c3c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PIntNumBaseChange.lean#L37-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PIntNumBaseChange.lean#L37-L42

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

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_coeffForm_monomial_6aa346b05c3c (φ : F' →ₗ[F] F) (μ : σ →₀ ℕ) (a : F') :
    coeffForm φ (monomial μ a) = monomial μ (φ a) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«coeffForm_monomial» := P2M_GroundTheory_Heights__Heights_FieldNumbers_coeffForm_monomial_6aa346b05c3c
