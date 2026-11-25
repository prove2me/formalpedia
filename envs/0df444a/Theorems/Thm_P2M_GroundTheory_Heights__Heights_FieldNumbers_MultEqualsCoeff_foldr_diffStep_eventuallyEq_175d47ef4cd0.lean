-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_MultEqualsCoeff_foldr_diffStep_eventuallyEq_175d47ef4cd0
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_MultEqualsCoeff_foldr_diffStep_eventuallyEq_175d47ef4cd0
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T03:17:12.413747+00:00
-- url     : https://prove2.me/theorems/cd0ba3b0-c322-4eba-911d-168dd06bd49f
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers Mult Equals Coeff foldr diff Step eventually Eq 175d47ef4cd0: P2 M Ground Theory Heights  Heights Field Numbers Mult Equals Coeff foldr diff Step even
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers Mult Equals Coeff foldr diff Step eventually Eq 175d47ef4cd0 construction uses the P2 M Ground Theory Heights  Heights Field Numbers Mult Equals Coeff foldr diff Step eventually Eq 175d47ef4cd0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PMultEqualsCoeff.lean#L45-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PMultEqualsCoeff.lean#L45-L52

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

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_MultEqualsCoeff_foldr_diffStep_eventuallyEq_175d47ef4cd0 {h g : (K → ℤ) → ℤ} (e : h =ᶠ[atTop] g) :
    ∀ L : List (K → ℤ), L.foldr diffStep h =ᶠ[atTop] L.foldr diffStep g
  := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«MultEqualsCoeff».«foldr_diffStep_eventuallyEq» := P2M_GroundTheory_Heights__Heights_FieldNumbers_MultEqualsCoeff_foldr_diffStep_eventuallyEq_175d47ef4cd0
