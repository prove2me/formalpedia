-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_finite_monomials_of_multidegree_04d4ee134769
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_finite_monomials_of_multidegree_04d4ee134769
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:28:40.1984+00:00
-- url     : https://prove2.me/theorems/ec4b9901-bfe4-4913-ad11-f411818e549b
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers finite monomials of multidegree 04d4ee134769: P2 M Ground Theory Heights  Heights Field Numbers finite monomials of multidegree 04d4ee134769
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers finite monomials of multidegree 04d4ee134769 construction uses the P2 M Ground Theory Heights  Heights Field Numbers finite monomials of multidegree 04d4ee134769 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PGradedFinite.lean#L15-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PGradedFinite.lean#L15-L22

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PGradedFinite
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

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_finite_monomials_of_multidegree_04d4ee134769 (m : K → ℕ) :
    {d : (Σ k, ι k) →₀ ℕ | Finsupp.weight (blockWeight ι) d = m}.Finite := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«finite_monomials_of_multidegree» := P2M_GroundTheory_Heights__Heights_FieldNumbers_finite_monomials_of_multidegree_04d4ee134769
