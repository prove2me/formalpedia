-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_map_eq_maximalIdeal_of_isRadical_fa5b08ef435e
-- name    : P2M_GroundTheory_Heights__Heights_map_eq_maximalIdeal_of_isRadical_fa5b08ef435e
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:57:27.947689+00:00
-- url     : https://prove2.me/theorems/c8eabab6-7f3a-42fa-b483-c507bfc52999
-- title:
--   P2 M Ground Theory Heights  Heights map eq maximal Ideal of is Radical fa5b08ef435e: P2 M Ground Theory Heights  Heights map eq maximal Ideal of is Radical fa5b08ef435e
-- statement:
--   The P2 M Ground Theory Heights  Heights map eq maximal Ideal of is Radical fa5b08ef435e construction uses the P2 M Ground Theory Heights  Heights map eq maximal Ideal of is Radical fa5b08ef435e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LocalMultRadical.lean#L9-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LocalMultRadical.lean#L9-L14

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LocalMultRadical
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial

theorem P2M_GroundTheory_Heights__Heights_map_eq_maximalIdeal_of_isRadical_fa5b08ef435e {A : Type*} [CommRing A] {J W : Ideal A} [W.IsPrime]
    (hJ : J.IsRadical) (hW : W ∈ J.minimalPrimes) :
    J.map (algebraMap A (Localization.AtPrime W)) = IsLocalRing.maximalIdeal (Localization.AtPrime W) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«map_eq_maximalIdeal_of_isRadical» := P2M_GroundTheory_Heights__Heights_map_eq_maximalIdeal_of_isRadical_fa5b08ef435e
