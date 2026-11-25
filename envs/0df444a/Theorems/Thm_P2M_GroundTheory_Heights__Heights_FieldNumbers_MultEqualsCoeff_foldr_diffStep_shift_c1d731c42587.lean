-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_MultEqualsCoeff_foldr_diffStep_shift_c1d731c42587
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_MultEqualsCoeff_foldr_diffStep_shift_c1d731c42587
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:18:20.280052+00:00
-- url     : https://prove2.me/theorems/4e214ba4-68da-5f27-ab93-60b84efc896d
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers Mult Equals Coeff foldr diff Step shift c1d731c42587: P2 M Ground Theory Heights  Heights Field Numbers Mult Equals Coeff foldr diff Step shift c1d731
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers Mult Equals Coeff foldr diff Step shift c1d731c42587 construction uses the P2 M Ground Theory Heights  Heights Field Numbers Mult Equals Coeff foldr diff Step shift c1d731c42587 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PMultEqualsCoeff.lean#L35-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PMultEqualsCoeff.lean#L35-L43

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

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_MultEqualsCoeff_foldr_diffStep_shift_c1d731c42587 (h : (K → ℤ) → ℤ) (c : K → ℤ) :
    ∀ L : List (K → ℤ),
      L.foldr diffStep (fun m => h (m - c)) = fun m => L.foldr diffStep h (m - c)
  := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«MultEqualsCoeff».«foldr_diffStep_shift» := P2M_GroundTheory_Heights__Heights_FieldNumbers_MultEqualsCoeff_foldr_diffStep_shift_c1d731c42587
