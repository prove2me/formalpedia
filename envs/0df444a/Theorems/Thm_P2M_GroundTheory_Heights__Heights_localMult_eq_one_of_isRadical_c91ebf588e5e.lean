-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_localMult_eq_one_of_isRadical_c91ebf588e5e
-- name    : P2M_GroundTheory_Heights__Heights_localMult_eq_one_of_isRadical_c91ebf588e5e
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:06:43.317844+00:00
-- url     : https://prove2.me/theorems/1e4942ea-36f7-46bf-a909-c729869bb485
-- title:
--   P2 M Ground Theory Heights  Heights local Mult eq one of is Radical c91ebf588e5e: P2 M Ground Theory Heights  Heights local Mult eq one of is Radical c91ebf588e5e
-- statement:
--   The P2 M Ground Theory Heights  Heights local Mult eq one of is Radical c91ebf588e5e construction uses the P2 M Ground Theory Heights  Heights local Mult eq one of is Radical c91ebf588e5e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LocalMultRadical.lean#L16-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LocalMultRadical.lean#L16-L25

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

theorem P2M_GroundTheory_Heights__Heights_localMult_eq_one_of_isRadical_c91ebf588e5e {A : Type*} [CommRing A] {J W : Ideal A} (hJ : J.IsRadical)
    (hW : W ∈ J.minimalPrimes) : localMult J W = 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«localMult_eq_one_of_isRadical» := P2M_GroundTheory_Heights__Heights_localMult_eq_one_of_isRadical_c91ebf588e5e
