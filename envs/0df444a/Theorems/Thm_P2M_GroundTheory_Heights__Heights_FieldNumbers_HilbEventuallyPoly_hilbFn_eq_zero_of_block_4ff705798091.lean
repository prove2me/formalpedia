-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_HilbEventuallyPoly_hilbFn_eq_zero_of_block_4ff705798091
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_HilbEventuallyPoly_hilbFn_eq_zero_of_block_4ff705798091
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:16:45.603558+00:00
-- url     : https://prove2.me/theorems/171a27c4-2ea2-5be1-b847-6342559b9cdf
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers Hilb Eventually Poly hilb Fn eq zero of block 4ff705798091: P2 M Ground Theory Heights  Heights Field Numbers Hilb Eventually Poly hilb Fn eq zero of
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers Hilb Eventually Poly hilb Fn eq zero of block 4ff705798091 construction uses the P2 M Ground Theory Heights  Heights Field Numbers Hilb Eventually Poly hilb Fn eq zero of block 4ff705798091 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/HilbEventuallyPolyQualified.lean#L69-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/HilbEventuallyPolyQualified.lean#L69-L106

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

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_HilbEventuallyPoly_hilbFn_eq_zero_of_block_4ff705798091 {I : Ideal (MRing ι F)} (k : K)
    (hk : ∀ i, (X ⟨k, i⟩ : MRing ι F) ∈ I) (m : K → ℤ) (hm : 1 ≤ m k) : hilbFn I m = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«HilbEventuallyPoly».«hilbFn_eq_zero_of_block» := P2M_GroundTheory_Heights__Heights_FieldNumbers_HilbEventuallyPoly_hilbFn_eq_zero_of_block_4ff705798091
