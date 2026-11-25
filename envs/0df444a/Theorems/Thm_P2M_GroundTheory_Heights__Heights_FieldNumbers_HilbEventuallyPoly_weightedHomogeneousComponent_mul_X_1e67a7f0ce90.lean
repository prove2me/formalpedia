-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_HilbEventuallyPoly_weightedHomogeneousComponent_mul_X_1e67a7f0ce90
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_HilbEventuallyPoly_weightedHomogeneousComponent_mul_X_1e67a7f0ce90
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:17:08.964501+00:00
-- url     : https://prove2.me/theorems/54e96e6a-b012-51dd-b2de-54e56f810f05
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers Hilb Eventually Poly weighted Homogeneous Component mul X 1e67a7f0ce90: P2 M Ground Theory Heights  Heights Field Numbers Hilb Eventually Poly weighte
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers Hilb Eventually Poly weighted Homogeneous Component mul X 1e67a7f0ce90 construction uses the P2 M Ground Theory Heights  Heights Field Numbers Hilb Eventually Poly weighted Homogeneous Component mul X 1e67a7f0ce90 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/HilbEventuallyPolyQualified.lean#L39-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/HilbEventuallyPolyQualified.lean#L39-L50

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

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_HilbEventuallyPoly_weightedHomogeneousComponent_mul_X_1e67a7f0ce90 (f : MRing ι F) (b : K → ℕ) (v : Σ k, ι k) :
    weightedHomogeneousComponent (blockWeight ι) (b + blockWeight ι v) (f * X v) =
      weightedHomogeneousComponent (blockWeight ι) b f * X v := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«HilbEventuallyPoly».«weightedHomogeneousComponent_mul_X» := P2M_GroundTheory_Heights__Heights_FieldNumbers_HilbEventuallyPoly_weightedHomogeneousComponent_mul_X_1e67a7f0ce90
