-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_finiteType_quotient_mRing_b4970ef5014b
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_finiteType_quotient_mRing_b4970ef5014b
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T07:05:21.424481+00:00
-- url     : https://prove2.me/theorems/2919871d-2538-5365-b0b3-51aff32a30db
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers finite Type quotient m Ring b4970ef5014b: P2 M Ground Theory Heights  Heights Field Numbers finite Type quotient m Ring b4970ef5014b
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers finite Type quotient m Ring b4970ef5014b construction uses the P2 M Ground Theory Heights  Heights Field Numbers finite Type quotient m Ring b4970ef5014b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PDegZeroLocDim.lean#L21-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PDegZeroLocDim.lean#L21-L22

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsMChart
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PDegZeroLocDim
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
variable {F : Type u} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
  [∀ k, Fintype (ι k)]
omit [DecidableEq K]

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_finiteType_quotient_mRing_b4970ef5014b (I : Ideal (MRing ι F)) : Algebra.FiniteType F (MRing ι F ⧸ I) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«finiteType_quotient_mRing» := P2M_GroundTheory_Heights__Heights_FieldNumbers_finiteType_quotient_mRing_b4970ef5014b
