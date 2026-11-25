-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_mem_nonZeroDivisors_of_notMem_of_minimalPrimes_eq_6b854b8a0529
-- name    : P2M_GroundTheory_Heights__Heights_mem_nonZeroDivisors_of_notMem_of_minimalPrimes_eq_6b854b8a0529
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T04:49:33.69649+00:00
-- url     : https://prove2.me/theorems/a7c2b05a-8aaa-49ff-b26c-d217b0720c17
-- title:
--   P2 M Ground Theory Heights  Heights mem non Zero Divisors of not Mem of minimal Primes eq 6b854b8a0529: P2 M Ground Theory Heights  Heights mem non Zero Divisors of not Mem of minimal Primes eq 6b854b
-- statement:
--   The P2 M Ground Theory Heights  Heights mem non Zero Divisors of not Mem of minimal Primes eq 6b854b8a0529 construction uses the P2 M Ground Theory Heights  Heights mem non Zero Divisors of not Mem of minimal Primes eq 6b854b8a0529 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PCMLengthParameters.lean#L14-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PCMLengthParameters.lean#L14-L21

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCMLengthParameters
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCMRegularElement
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLengthLocalizedQuotient
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_RegularLocalDomain
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCMLengthParameters
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
open IsLocalRing
universe u

theorem P2M_GroundTheory_Heights__Heights_mem_nonZeroDivisors_of_notMem_of_minimalPrimes_eq_6b854b8a0529 (hCM : CMRegularElement.Statement.{u})
    {B : Type u} [CommRing B] [IsCohenMacaulayLocalRing B] {P : Ideal B} (hmin : minimalPrimes B = {P})
    {s : B} (hs : s ∉ P) : s ∈ nonZeroDivisors B := by sorry

alias «GroundTheory».«Heights₂».«Heights».«mem_nonZeroDivisors_of_notMem_of_minimalPrimes_eq» := P2M_GroundTheory_Heights__Heights_mem_nonZeroDivisors_of_notMem_of_minimalPrimes_eq_6b854b8a0529
