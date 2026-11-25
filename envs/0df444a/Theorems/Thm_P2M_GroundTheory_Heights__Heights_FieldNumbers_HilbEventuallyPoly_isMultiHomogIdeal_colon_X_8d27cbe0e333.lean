-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_HilbEventuallyPoly_isMultiHomogIdeal_colon_X_8d27cbe0e333
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_HilbEventuallyPoly_isMultiHomogIdeal_colon_X_8d27cbe0e333
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:16:37.75829+00:00
-- url     : https://prove2.me/theorems/c58bfbce-66be-4510-bc40-210be4a3cd1e
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers Hilb Eventually Poly is Multi Homog Ideal colon X 8d27cbe0e333: P2 M Ground Theory Heights  Heights Field Numbers Hilb Eventually Poly is Multi Homog
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers Hilb Eventually Poly is Multi Homog Ideal colon X 8d27cbe0e333 construction uses the P2 M Ground Theory Heights  Heights Field Numbers Hilb Eventually Poly is Multi Homog Ideal colon X 8d27cbe0e333 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/HilbEventuallyPolyQualified.lean#L52-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/HilbEventuallyPolyQualified.lean#L52-L57

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

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_HilbEventuallyPoly_isMultiHomogIdeal_colon_X_8d27cbe0e333 {I : Ideal (MRing ι F)} (hI : IsMultiHomogIdeal I)
    (v : Σ k, ι k) : IsMultiHomogIdeal (I.colon (Ideal.span {(X v : MRing ι F)})) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«HilbEventuallyPoly».«isMultiHomogIdeal_colon_X» := P2M_GroundTheory_Heights__Heights_FieldNumbers_HilbEventuallyPoly_isMultiHomogIdeal_colon_X_8d27cbe0e333
