-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_HilbEventuallyPoly_eval_shift_c0b41e6fe1b0
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_HilbEventuallyPoly_eval_shift_c0b41e6fe1b0
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:16:35.062333+00:00
-- url     : https://prove2.me/theorems/01d50314-313b-4f90-a62d-4c11bb55ed6c
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers Hilb Eventually Poly eval shift c0b41e6fe1b0: P2 M Ground Theory Heights  Heights Field Numbers Hilb Eventually Poly eval shift c0b41e6fe1b0
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers Hilb Eventually Poly eval shift c0b41e6fe1b0 construction uses the P2 M Ground Theory Heights  Heights Field Numbers Hilb Eventually Poly eval shift c0b41e6fe1b0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/HilbEventuallyPolyQualified.lean#L122-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/HilbEventuallyPolyQualified.lean#L122-L130

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_HilbEventuallyPolyQualified
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
open GroundTheory.Heights₂.Heights.FieldNumbers.HilbEventuallyPoly
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} {F : Type*} [Field F]
attribute [local instance] MvPolynomial.weightedGradedAlgebra
omit [Fintype K] [DecidableEq K]

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_HilbEventuallyPoly_eval_shift_c0b41e6fe1b0 (p : MvPolynomial K ℚ) (e m : K → ℤ) :
    eval (fun k => ((m - e) k : ℚ)) p =
      eval (fun k => (m k : ℚ)) (bind₁ (fun j => X j - C ((e j : ℤ) : ℚ)) p) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«HilbEventuallyPoly».«eval_shift» := P2M_GroundTheory_Heights__Heights_FieldNumbers_HilbEventuallyPoly_eval_shift_c0b41e6fe1b0
