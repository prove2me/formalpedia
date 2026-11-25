-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_map_mem_associatedPrimes_quotient_51d6dc3f0828
-- name    : P2M_GroundTheory_Heights__Heights_map_mem_associatedPrimes_quotient_51d6dc3f0828
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:48:49.080827+00:00
-- url     : https://prove2.me/theorems/09e479f0-715d-462c-a24b-ab3afa322cc7
-- title:
--   P2 M Ground Theory Heights  Heights map mem associated Primes quotient 51d6dc3f0828: P2 M Ground Theory Heights  Heights map mem associated Primes quotient 51d6dc3f0828
-- statement:
--   The P2 M Ground Theory Heights  Heights map mem associated Primes quotient 51d6dc3f0828 construction uses the P2 M Ground Theory Heights  Heights map mem associated Primes quotient 51d6dc3f0828 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PCMQuotientUnmixed.lean#L11-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PCMQuotientUnmixed.lean#L11-L29

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCMQuotientUnmixed
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCMParameterQuotient
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCMRingUnmixed
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCMQuotientUnmixed
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

theorem P2M_GroundTheory_Heights__Heights_map_mem_associatedPrimes_quotient_51d6dc3f0828 {B : Type*} [CommRing B] [IsNoetherianRing B] (I p : Ideal B)
    (hp : p ∈ associatedPrimes B (B ⧸ I)) :
    I ≤ p ∧ p.map (Ideal.Quotient.mk I) ∈ associatedPrimes (B ⧸ I) (B ⧸ I) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«map_mem_associatedPrimes_quotient» := P2M_GroundTheory_Heights__Heights_map_mem_associatedPrimes_quotient_51d6dc3f0828
