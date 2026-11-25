-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_BaseChangeAvoid_comap_eq_of_mem_minimalPrimes_4b21b6da26c6
-- name    : P2M_GroundTheory_Heights__Heights_BaseChangeAvoid_comap_eq_of_mem_minimalPrimes_4b21b6da26c6
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T00:15:27.813894+00:00
-- url     : https://prove2.me/theorems/9ecddc0a-5e41-453e-b324-95e0d5eb8cdc
-- title:
--   P2 M Ground Theory Heights  Heights Base Change Avoid comap eq of mem minimal Primes 4b21b6da26c6: P2 M Ground Theory Heights  Heights Base Change Avoid comap eq of mem minimal Primes 4b21b6da26c6
-- statement:
--   The P2 M Ground Theory Heights  Heights Base Change Avoid comap eq of mem minimal Primes 4b21b6da26c6 construction uses the P2 M Ground Theory Heights  Heights Base Change Avoid comap eq of mem minimal Primes 4b21b6da26c6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PBaseChangeAvoid.lean#L9-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PBaseChangeAvoid.lean#L9-L30

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ConeBall
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PBaseChangeAvoid
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

theorem P2M_GroundTheory_Heights__Heights_BaseChangeAvoid_comap_eq_of_mem_minimalPrimes_4b21b6da26c6 {K L : Type*} [Field K] [Field L] {n : ℕ}
    (σ : K →+* L) (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    {W : Ideal (MvPolynomial (Fin n) L)} (hW : W ∈ (I.map (MvPolynomial.map σ)).minimalPrimes) :
    W.comap (MvPolynomial.map σ) = I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«BaseChangeAvoid».«comap_eq_of_mem_minimalPrimes» := P2M_GroundTheory_Heights__Heights_BaseChangeAvoid_comap_eq_of_mem_minimalPrimes_4b21b6da26c6
