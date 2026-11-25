-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_sum_smul_mk_monomial_4718e7a55a19
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_sum_smul_mk_monomial_4718e7a55a19
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:03:00.563523+00:00
-- url     : https://prove2.me/theorems/9d848d65-1f99-415d-af08-7ac3c63e6c9d
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers sum smul mk monomial 4718e7a55a19: P2 M Ground Theory Heights  Heights Field Numbers sum smul mk monomial 4718e7a55a19
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers sum smul mk monomial 4718e7a55a19 construction uses the P2 M Ground Theory Heights  Heights Field Numbers sum smul mk monomial 4718e7a55a19 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PIntNumBaseChange.lean#L187-L192
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PIntNumBaseChange.lean#L187-L192

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
omit [Fintype K] [DecidableEq K] [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_sum_smul_mk_monomial_4718e7a55a19 (E : Type*) [Field E] (J : Ideal (MRing ι E)) {B : Type*} [Fintype B]
    (lift : B → (Σ k, ι k) →₀ ℕ) (c : B → E) :
    ∑ x, c x • Ideal.Quotient.mk J (monomial (lift x) (1 : E)) =
      Ideal.Quotient.mk J (∑ x, monomial (lift x) (c x)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«sum_smul_mk_monomial» := P2M_GroundTheory_Heights__Heights_FieldNumbers_sum_smul_mk_monomial_4718e7a55a19
