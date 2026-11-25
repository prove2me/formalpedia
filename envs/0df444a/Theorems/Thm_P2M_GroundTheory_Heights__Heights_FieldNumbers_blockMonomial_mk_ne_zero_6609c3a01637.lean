-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_blockMonomial_mk_ne_zero_6609c3a01637
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_blockMonomial_mk_ne_zero_6609c3a01637
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:17:31.048945+00:00
-- url     : https://prove2.me/theorems/11d833a7-3332-4f8e-b0c7-1523b3e56152
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers block Monomial mk ne zero 6609c3a01637: P2 M Ground Theory Heights  Heights Field Numbers block Monomial mk ne zero 6609c3a01637
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers block Monomial mk ne zero 6609c3a01637 construction uses the P2 M Ground Theory Heights  Heights Field Numbers block Monomial mk ne zero 6609c3a01637 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PIntNumBase.lean#L43-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PIntNumBase.lean#L43-L52

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PGradedFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PIntNumBase
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

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_blockMonomial_mk_ne_zero_6609c3a01637 (P : Ideal (MRing ι F)) [P.IsPrime] (i : ∀ k, ι k)
    (hi : ∀ k, (X ⟨k, i k⟩ : MRing ι F) ∉ P) (m : K → ℕ) :
    Ideal.Quotient.mk P (blockMonomial i m) ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«blockMonomial_mk_ne_zero» := P2M_GroundTheory_Heights__Heights_FieldNumbers_blockMonomial_mk_ne_zero_6609c3a01637
