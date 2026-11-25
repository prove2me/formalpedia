-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_MultEqualsCoeff_exists_nat_of_nonneg_of_lt_1bce399617db
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_MultEqualsCoeff_exists_nat_of_nonneg_of_lt_1bce399617db
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:18:16.370032+00:00
-- url     : https://prove2.me/theorems/8180e082-8138-47b6-a6ae-0c1217e4acee
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers Mult Equals Coeff exists nat of nonneg of lt 1bce399617db: P2 M Ground Theory Heights  Heights Field Numbers Mult Equals Coeff exists nat of nonneg of
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers Mult Equals Coeff exists nat of nonneg of lt 1bce399617db construction uses the P2 M Ground Theory Heights  Heights Field Numbers Mult Equals Coeff exists nat of nonneg of lt 1bce399617db property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PMultEqualsCoeff.lean#L54-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PMultEqualsCoeff.lean#L54-L65

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

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_MultEqualsCoeff_exists_nat_of_nonneg_of_lt_1bce399617db {x : WithBot (WithTop ℤ)} {n : ℕ} (h0 : 0 ≤ x)
    (h : x < n) : ∃ d : ℕ, x = d ∧ d < n := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«MultEqualsCoeff».«exists_nat_of_nonneg_of_lt» := P2M_GroundTheory_Heights__Heights_FieldNumbers_MultEqualsCoeff_exists_nat_of_nonneg_of_lt_1bce399617db
