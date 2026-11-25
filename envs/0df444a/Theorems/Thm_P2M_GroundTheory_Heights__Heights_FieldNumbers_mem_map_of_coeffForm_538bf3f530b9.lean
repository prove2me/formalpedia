-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_mem_map_of_coeffForm_538bf3f530b9
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_mem_map_of_coeffForm_538bf3f530b9
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:18:07.233727+00:00
-- url     : https://prove2.me/theorems/212c4445-4d99-478e-81b7-57807dc3ace2
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers mem map of coeff Form 538bf3f530b9: P2 M Ground Theory Heights  Heights Field Numbers mem map of coeff Form 538bf3f530b9
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers mem map of coeff Form 538bf3f530b9 construction uses the P2 M Ground Theory Heights  Heights Field Numbers mem map of coeff Form 538bf3f530b9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PIntNumBaseChange.lean#L111-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PIntNumBaseChange.lean#L111-L131

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

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_mem_map_of_coeffForm_538bf3f530b9 {I : Ideal (MvPolynomial σ F)} {f : MvPolynomial σ F'}
    (h : ∀ φ : F' →ₗ[F] F, coeffForm φ f ∈ I) : f ∈ I.map (map (algebraMap F F')) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«mem_map_of_coeffForm» := P2M_GroundTheory_Heights__Heights_FieldNumbers_mem_map_of_coeffForm_538bf3f530b9
