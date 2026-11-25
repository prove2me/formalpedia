-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_mem_nonZeroDivisors_of_not_mem_minimalPrimes_5ade1a33ecea
-- name    : P2M_GroundTheory_Heights__Heights_mem_nonZeroDivisors_of_not_mem_minimalPrimes_5ade1a33ecea
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T04:49:05.754906+00:00
-- url     : https://prove2.me/theorems/ff15f334-b98b-49d3-9c50-16b946e3e6ad
-- title:
--   P2 M Ground Theory Heights  Heights mem non Zero Divisors of not mem minimal Primes 5ade1a33ecea: P2 M Ground Theory Heights  Heights mem non Zero Divisors of not mem minimal Primes 5ade1a33ecea
-- statement:
--   The P2 M Ground Theory Heights  Heights mem non Zero Divisors of not mem minimal Primes 5ade1a33ecea construction uses the P2 M Ground Theory Heights  Heights mem non Zero Divisors of not mem minimal Primes 5ade1a33ecea property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PCMRegularElement.lean#L53-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PCMRegularElement.lean#L53-L59

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCMRegularElement
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_CMDepthAssoc
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCMRegularElement
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
open IsLocalRing RingTheory.Sequence CategoryTheory Abelian Limits Pointwise
universe u

theorem P2M_GroundTheory_Heights__Heights_mem_nonZeroDivisors_of_not_mem_minimalPrimes_5ade1a33ecea {B : Type*} [CommRing B] [IsCohenMacaulayLocalRing B] {y : B}
    (hy : ∀ p ∈ minimalPrimes B, y ∉ p) : y ∈ nonZeroDivisors B := by sorry

alias «GroundTheory».«Heights₂».«Heights».«mem_nonZeroDivisors_of_not_mem_minimalPrimes» := P2M_GroundTheory_Heights__Heights_mem_nonZeroDivisors_of_not_mem_minimalPrimes_5ade1a33ecea
