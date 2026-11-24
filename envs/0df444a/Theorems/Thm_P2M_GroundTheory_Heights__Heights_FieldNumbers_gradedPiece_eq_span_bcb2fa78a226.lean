-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_gradedPiece_eq_span_bcb2fa78a226
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_gradedPiece_eq_span_bcb2fa78a226
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:34:39.998594+00:00
-- url     : https://prove2.me/theorems/139b41a6-40be-46dc-a1ff-dca6a1ddebd7
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers graded Piece eq span bcb2fa78a226: P2 M Ground Theory Heights  Heights Field Numbers graded Piece eq span bcb2fa78a226
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers graded Piece eq span bcb2fa78a226 construction uses the P2 M Ground Theory Heights  Heights Field Numbers graded Piece eq span bcb2fa78a226 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PIntNumBaseChange.lean#L158-L177
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PIntNumBaseChange.lean#L158-L177

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
variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} [∀ k, Fintype (ι k)]
omit [Fintype K] [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_gradedPiece_eq_span_bcb2fa78a226 (E : Type*) [Field E] (J : Ideal (MRing ι E)) (m : K → ℕ) :
    gradedPiece J m = Submodule.span E ((fun d => Ideal.Quotient.mk J (monomial d (1 : E))) ''
      {d : (Σ k, ι k) →₀ ℕ | Finsupp.weight (blockWeight ι) d = m}) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«gradedPiece_eq_span» := P2M_GroundTheory_Heights__Heights_FieldNumbers_gradedPiece_eq_span_bcb2fa78a226
