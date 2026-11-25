-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_HilbEventuallyPoly_cast_single_504a09db5994
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_HilbEventuallyPoly_cast_single_504a09db5994
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:17:24.039913+00:00
-- url     : https://prove2.me/theorems/469802ce-401a-42e5-b9ae-6c0d286f8cfc
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers Hilb Eventually Poly cast single 504a09db5994: P2 M Ground Theory Heights  Heights Field Numbers Hilb Eventually Poly cast single 504a09db5994
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers Hilb Eventually Poly cast single 504a09db5994 construction uses the P2 M Ground Theory Heights  Heights Field Numbers Hilb Eventually Poly cast single 504a09db5994 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/HilbEventuallyPolyQualified.lean#L134-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/HilbEventuallyPolyQualified.lean#L134-L139

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
omit [Fintype K]

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_HilbEventuallyPoly_cast_single_504a09db5994 (k : K) :
    (fun k' => (((Pi.single k 1 : K → ℕ) k' : ℕ) : ℤ)) = Pi.single k 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«HilbEventuallyPoly».«cast_single» := P2M_GroundTheory_Heights__Heights_FieldNumbers_HilbEventuallyPoly_cast_single_504a09db5994
