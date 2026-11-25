-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_coeffForm_mem_0f251d0f8cfe
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_coeffForm_mem_0f251d0f8cfe
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:31:59.511562+00:00
-- url     : https://prove2.me/theorems/6862a263-5f16-4216-b116-4860864542d1
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers coeff Form mem 0f251d0f8cfe: P2 M Ground Theory Heights  Heights Field Numbers coeff Form mem 0f251d0f8cfe
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers coeff Form mem 0f251d0f8cfe construction uses the P2 M Ground Theory Heights  Heights Field Numbers coeff Form mem 0f251d0f8cfe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PIntNumBaseChange.lean#L68-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PIntNumBaseChange.lean#L68-L86

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

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_coeffForm_mem_0f251d0f8cfe (φ : F' →ₗ[F] F) {I : Ideal (MvPolynomial σ F)} {f : MvPolynomial σ F'}
    (hf : f ∈ I.map (map (algebraMap F F'))) : coeffForm φ f ∈ I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«coeffForm_mem» := P2M_GroundTheory_Heights__Heights_FieldNumbers_coeffForm_mem_0f251d0f8cfe
