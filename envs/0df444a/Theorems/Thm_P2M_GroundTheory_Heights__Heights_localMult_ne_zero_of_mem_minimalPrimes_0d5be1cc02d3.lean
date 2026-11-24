-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_localMult_ne_zero_of_mem_minimalPrimes_0d5be1cc02d3
-- name    : P2M_GroundTheory_Heights__Heights_localMult_ne_zero_of_mem_minimalPrimes_0d5be1cc02d3
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:47:33.748789+00:00
-- url     : https://prove2.me/theorems/02377d08-cc8b-49a2-8296-4aed82709e2f
-- title:
--   P2 M Ground Theory Heights  Heights local Mult ne zero of mem minimal Primes 0d5be1cc02d3: P2 M Ground Theory Heights  Heights local Mult ne zero of mem minimal Primes 0d5be1cc02d3
-- statement:
--   The P2 M Ground Theory Heights  Heights local Mult ne zero of mem minimal Primes 0d5be1cc02d3 construction uses the P2 M Ground Theory Heights  Heights local Mult ne zero of mem minimal Primes 0d5be1cc02d3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PProperSymm.lean#L9-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PProperSymm.lean#L9-L27

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsMahler
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PProperSymm
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
open MvPolynomial Ideal

theorem P2M_GroundTheory_Heights__Heights_localMult_ne_zero_of_mem_minimalPrimes_0d5be1cc02d3 {A : Type*} [CommRing A] [IsNoetherianRing A]
    {J P : Ideal A} (hP : P ∈ J.minimalPrimes) : localMult J P ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«localMult_ne_zero_of_mem_minimalPrimes» := P2M_GroundTheory_Heights__Heights_localMult_ne_zero_of_mem_minimalPrimes_0d5be1cc02d3
