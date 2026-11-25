-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_dvd_pow_of_ne_zero_of_not_isUnit_81bea8ad7a4b
-- name    : P2M_GroundTheory_Heights__Heights_Vertical_dvd_pow_of_ne_zero_of_not_isUnit_81bea8ad7a4b
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T04:45:25.443949+00:00
-- url     : https://prove2.me/theorems/fcbd374a-89bb-4b4c-8f93-8820a6327156
-- title:
--   P2 M Ground Theory Heights  Heights Vertical dvd pow of ne zero of not is Unit 81bea8ad7a4b: P2 M Ground Theory Heights  Heights Vertical dvd pow of ne zero of not is Unit 81bea8ad7a4b
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical dvd pow of ne zero of not is Unit 81bea8ad7a4b construction uses the P2 M Ground Theory Heights  Heights Vertical dvd pow of ne zero of not is Unit 81bea8ad7a4b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PSecBTorsionFree.lean#L334-L345
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PSecBTorsionFree.lean#L334-L345

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_IntToFracInjective
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PSecBTorsionFree
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Vertical
open MvPolynomial NumberField IsDedekindDomain
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_Vertical_dvd_pow_of_ne_zero_of_not_isUnit_81bea8ad7a4b {R : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {r x : R} (hr : r ≠ 0) (hx : x ≠ 0) (hxu : ¬IsUnit x) :
    ∃ k : ℕ, r ∣ x ^ k := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Vertical».«dvd_pow_of_ne_zero_of_not_isUnit» := P2M_GroundTheory_Heights__Heights_Vertical_dvd_pow_of_ne_zero_of_not_isUnit_81bea8ad7a4b
