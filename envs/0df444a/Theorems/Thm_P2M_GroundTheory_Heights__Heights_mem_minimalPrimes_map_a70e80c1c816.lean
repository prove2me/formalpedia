-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_mem_minimalPrimes_map_a70e80c1c816
-- name    : P2M_GroundTheory_Heights__Heights_mem_minimalPrimes_map_a70e80c1c816
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T04:49:10.745933+00:00
-- url     : https://prove2.me/theorems/2ffd80d4-5c77-403a-8cb0-fed3157cb73a
-- title:
--   P2 M Ground Theory Heights  Heights mem minimal Primes map a70e80c1c816: P2 M Ground Theory Heights  Heights mem minimal Primes map a70e80c1c816
-- statement:
--   The P2 M Ground Theory Heights  Heights mem minimal Primes map a70e80c1c816 construction uses the P2 M Ground Theory Heights  Heights mem minimal Primes map a70e80c1c816 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PFundCycleBaseChange.lean#L64-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PFundCycleBaseChange.lean#L64-L77

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

theorem P2M_GroundTheory_Heights__Heights_mem_minimalPrimes_map_a70e80c1c816 {J W : Ideal A} (hW : W ∈ J.minimalPrimes) {P : Ideal B}
    (hP : P ∈ (W.map f).minimalPrimes) : P ∈ (J.map f).minimalPrimes := by sorry

alias «GroundTheory».«Heights₂».«Heights».«mem_minimalPrimes_map» := P2M_GroundTheory_Heights__Heights_mem_minimalPrimes_map_a70e80c1c816
