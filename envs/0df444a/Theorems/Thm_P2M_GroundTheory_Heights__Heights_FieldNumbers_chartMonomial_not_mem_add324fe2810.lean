-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_chartMonomial_not_mem_add324fe2810
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_chartMonomial_not_mem_add324fe2810
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T07:52:08.716832+00:00
-- url     : https://prove2.me/theorems/081d6a73-9d8c-5784-9f52-54cff2a87b5b
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers chart Monomial not mem add324fe2810: P2 M Ground Theory Heights  Heights Field Numbers chart Monomial not mem add324fe2810
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers chart Monomial not mem add324fe2810 construction uses the P2 M Ground Theory Heights  Heights Field Numbers chart Monomial not mem add324fe2810 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PDegZeroLocDim.lean#L26-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PDegZeroLocDim.lean#L26-L31

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
omit [DecidableEq K] [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_chartMonomial_not_mem_add324fe2810 (Q : Ideal (MRing ι F)) [Q.IsPrime] (u : ∀ k, ι k)
    (hu : ∀ k, (X ⟨k, u k⟩ : MRing ι F) ∉ Q) (b : K → ℕ) : chartMonomial u b ∉ Q := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«chartMonomial_not_mem» := P2M_GroundTheory_Heights__Heights_FieldNumbers_chartMonomial_not_mem_add324fe2810
