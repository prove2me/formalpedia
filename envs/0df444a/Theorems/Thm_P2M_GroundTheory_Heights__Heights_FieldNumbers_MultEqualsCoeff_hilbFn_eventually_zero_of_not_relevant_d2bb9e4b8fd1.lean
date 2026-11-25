-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_MultEqualsCoeff_hilbFn_eventually_zero_of_not_relevant_d2bb9e4b8fd1
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_MultEqualsCoeff_hilbFn_eventually_zero_of_not_relevant_d2bb9e4b8fd1
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T03:17:34.847057+00:00
-- url     : https://prove2.me/theorems/eccf0c41-eb3e-4667-847f-0949347f5f88
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers Mult Equals Coeff hilb Fn eventually zero of not relevant d2bb9e4b8fd1: P2 M Ground Theory Heights  Heights Field Numbers Mult Equals Coeff hilb Fn ev
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers Mult Equals Coeff hilb Fn eventually zero of not relevant d2bb9e4b8fd1 construction uses the P2 M Ground Theory Heights  Heights Field Numbers Mult Equals Coeff hilb Fn eventually zero of not relevant d2bb9e4b8fd1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PMultEqualsCoeff.lean#L87-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PMultEqualsCoeff.lean#L87-L125

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsDegreeBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PMultEqualsCoeff
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
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR Filter
universe u
open GroundTheory.Heights₂.Heights.FieldNumbers.MultEqualsCoeff
variable {K : Type*}
variable [Fintype K] [DecidableEq K] {ι : K → Type*} {F : Type*} [Field F]

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_MultEqualsCoeff_hilbFn_eventually_zero_of_not_relevant_d2bb9e4b8fd1 (I : Ideal (MRing ι F)) (hI : ¬ IsRelevant I) :
    ∀ᶠ m in atTop, hilbFn I m = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«MultEqualsCoeff».«hilbFn_eventually_zero_of_not_relevant» := P2M_GroundTheory_Heights__Heights_FieldNumbers_MultEqualsCoeff_hilbFn_eventually_zero_of_not_relevant_d2bb9e4b8fd1
