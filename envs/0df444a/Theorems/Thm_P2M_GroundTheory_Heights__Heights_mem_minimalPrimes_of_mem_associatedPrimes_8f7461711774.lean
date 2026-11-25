-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_mem_minimalPrimes_of_mem_associatedPrimes_8f7461711774
-- name    : P2M_GroundTheory_Heights__Heights_mem_minimalPrimes_of_mem_associatedPrimes_8f7461711774
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T04:49:06.132159+00:00
-- url     : https://prove2.me/theorems/0636adf8-ef2c-47e1-a95b-2232af1a1853
-- title:
--   P2 M Ground Theory Heights  Heights mem minimal Primes of mem associated Primes 8f7461711774: P2 M Ground Theory Heights  Heights mem minimal Primes of mem associated Primes 8f7461711774
-- statement:
--   The P2 M Ground Theory Heights  Heights mem minimal Primes of mem associated Primes 8f7461711774 construction uses the P2 M Ground Theory Heights  Heights mem minimal Primes of mem associated Primes 8f7461711774 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PCMRegularElement.lean#L12-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PCMRegularElement.lean#L12-L51

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

theorem P2M_GroundTheory_Heights__Heights_mem_minimalPrimes_of_mem_associatedPrimes_8f7461711774 {B : Type*} [CommRing B] [IsCohenMacaulayLocalRing B]
    {p : Ideal B} (hp : p ∈ associatedPrimes B B) : p ∈ minimalPrimes B := by sorry

alias «GroundTheory».«Heights₂».«Heights».«mem_minimalPrimes_of_mem_associatedPrimes» := P2M_GroundTheory_Heights__Heights_mem_minimalPrimes_of_mem_associatedPrimes_8f7461711774
