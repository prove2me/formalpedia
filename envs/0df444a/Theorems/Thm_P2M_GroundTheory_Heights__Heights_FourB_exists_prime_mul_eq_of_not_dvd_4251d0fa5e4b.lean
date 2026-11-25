-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FourB_exists_prime_mul_eq_of_not_dvd_4251d0fa5e4b
-- name    : P2M_GroundTheory_Heights__Heights_FourB_exists_prime_mul_eq_of_not_dvd_4251d0fa5e4b
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:36:56.210111+00:00
-- url     : https://prove2.me/theorems/74cadab1-4de2-505c-bb6a-3dad31979761
-- title:
--   P2 M Ground Theory Heights  Heights Four B exists prime mul eq of not dvd 4251d0fa5e4b: P2 M Ground Theory Heights  Heights Four B exists prime mul eq of not dvd 4251d0fa5e4b
-- statement:
--   The P2 M Ground Theory Heights  Heights Four B exists prime mul eq of not dvd 4251d0fa5e4b construction uses the P2 M Ground Theory Heights  Heights Four B exists prime mul eq of not dvd 4251d0fa5e4b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/PIntegralOnModel.lean#L11-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/PIntegralOnModel.lean#L11-L66

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_ToricVarieties_KrullDomain
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_StatementsIntegralPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_PIntegralOnModel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FourB
open IsDedekindDomain NumberField

theorem P2M_GroundTheory_Heights__Heights_FourB_exists_prime_mul_eq_of_not_dvd_4251d0fa5e4b {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [IsIntegrallyClosed A] {a b : A} (hab : ¬ b ∣ a) :
    ∃ P : Ideal A, P.IsPrime ∧ ∃ w ∉ P, ∃ c ∈ P, w * b = c * a := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FourB».«exists_prime_mul_eq_of_not_dvd» := P2M_GroundTheory_Heights__Heights_FourB_exists_prime_mul_eq_of_not_dvd_4251d0fa5e4b
