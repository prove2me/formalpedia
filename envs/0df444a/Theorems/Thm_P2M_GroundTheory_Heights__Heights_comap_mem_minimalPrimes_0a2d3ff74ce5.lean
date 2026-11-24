-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_comap_mem_minimalPrimes_0a2d3ff74ce5
-- name    : P2M_GroundTheory_Heights__Heights_comap_mem_minimalPrimes_0a2d3ff74ce5
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:29:18.190701+00:00
-- url     : https://prove2.me/theorems/101f4345-788c-4bd5-9507-d8fe035e95b3
-- title:
--   P2 M Ground Theory Heights  Heights comap mem minimal Primes 0a2d3ff74ce5: P2 M Ground Theory Heights  Heights comap mem minimal Primes 0a2d3ff74ce5
-- statement:
--   The P2 M Ground Theory Heights  Heights comap mem minimal Primes 0a2d3ff74ce5 construction uses the P2 M Ground Theory Heights  Heights comap mem minimal Primes 0a2d3ff74ce5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PFundCycleBaseChange.lean#L49-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PFundCycleBaseChange.lean#L49-L62

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsFundCycleBaseChange
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsMinimalPrimeComap
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PRadicalBaseChange
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LocalMultRadical
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PFundCycleBaseChange
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
variable {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B)
  (hc : ∀ I : Ideal A, I.IsPrime → ∀ P ∈ (I.map f).minimalPrimes, P.comap f = I)
include hc

theorem P2M_GroundTheory_Heights__Heights_comap_mem_minimalPrimes_0a2d3ff74ce5 {J : Ideal A} {P : Ideal B} (hP : P ∈ (J.map f).minimalPrimes) :
    P.comap f ∈ J.minimalPrimes ∧ P ∈ ((P.comap f).map f).minimalPrimes := by sorry

alias «GroundTheory».«Heights₂».«Heights».«comap_mem_minimalPrimes» := P2M_GroundTheory_Heights__Heights_comap_mem_minimalPrimes_0a2d3ff74ce5
