-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_MultEqualsCoeff_relDim_nonneg_of_card_le_18aa7f6b6ed1
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_MultEqualsCoeff_relDim_nonneg_of_card_le_18aa7f6b6ed1
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T03:18:37.99091+00:00
-- url     : https://prove2.me/theorems/b690f4b5-d76c-54a4-9c98-f91ba898b3f7
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers Mult Equals Coeff rel Dim nonneg of card le 18aa7f6b6ed1: P2 M Ground Theory Heights  Heights Field Numbers Mult Equals Coeff rel Dim nonneg of card l
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers Mult Equals Coeff rel Dim nonneg of card le 18aa7f6b6ed1 construction uses the P2 M Ground Theory Heights  Heights Field Numbers Mult Equals Coeff rel Dim nonneg of card le 18aa7f6b6ed1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PMultEqualsCoeff.lean#L71-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PMultEqualsCoeff.lean#L71-L85

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
omit [DecidableEq K]

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_MultEqualsCoeff_relDim_nonneg_of_card_le_18aa7f6b6ed1 (I : Ideal (MRing ι F))
    (h : ((Fintype.card K : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (MRing ι F ⧸ I)) : 0 ≤ relDim I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«MultEqualsCoeff».«relDim_nonneg_of_card_le» := P2M_GroundTheory_Heights__Heights_FieldNumbers_MultEqualsCoeff_relDim_nonneg_of_card_le_18aa7f6b6ed1
