-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_MultEqualsCoeff_foldr_diffStep_zero_cfe94599070f
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_MultEqualsCoeff_foldr_diffStep_zero_cfe94599070f
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T03:18:31.861127+00:00
-- url     : https://prove2.me/theorems/082c084d-d70d-58ec-a7e4-99d66cd8e6f3
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers Mult Equals Coeff foldr diff Step zero cfe94599070f: P2 M Ground Theory Heights  Heights Field Numbers Mult Equals Coeff foldr diff Step zero cfe94599
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers Mult Equals Coeff foldr diff Step zero cfe94599070f construction uses the P2 M Ground Theory Heights  Heights Field Numbers Mult Equals Coeff foldr diff Step zero cfe94599070f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PMultEqualsCoeff.lean#L28-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PMultEqualsCoeff.lean#L28-L33

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

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_MultEqualsCoeff_foldr_diffStep_zero_cfe94599070f : ∀ L : List (K → ℤ), L.foldr diffStep (0 : (K → ℤ) → ℤ) = 0
  := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«MultEqualsCoeff».«foldr_diffStep_zero» := P2M_GroundTheory_Heights__Heights_FieldNumbers_MultEqualsCoeff_foldr_diffStep_zero_cfe94599070f
