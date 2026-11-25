-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ringKrullDim_eq_one_of_surjective_of_ker_mem_minimalPrimes_db08cc59c2af
-- name    : P2M_GroundTheory_Heights__Heights_ringKrullDim_eq_one_of_surjective_of_ker_mem_minimalPrimes_db08cc59c2af
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:09:07.687191+00:00
-- url     : https://prove2.me/theorems/1dd58e39-8abe-5207-81df-8fa38960fc88
-- title:
--   P2 M Ground Theory Heights  Heights ring Krull Dim eq one of surjective of ker mem minimal Primes db08cc59c2af: P2 M Ground Theory Heights  Heights ring Krull Dim eq one of surjective of ker mem minim
-- statement:
--   The P2 M Ground Theory Heights  Heights ring Krull Dim eq one of surjective of ker mem minimal Primes db08cc59c2af construction uses the P2 M Ground Theory Heights  Heights ring Krull Dim eq one of surjective of ker mem minimal Primes db08cc59c2af property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PPlaceOnComponent.lean#L11-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PPlaceOnComponent.lean#L11-L31

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPlaceOnComponent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StReducedNormalisationPlace
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCurveMinimalPrimeQuotient
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPlaceOnComponent
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
open MvPolynomial ComplexSets

theorem P2M_GroundTheory_Heights__Heights_ringKrullDim_eq_one_of_surjective_of_ker_mem_minimalPrimes_db08cc59c2af {R S : Type*} [CommRing R] [CommRing S]
    [IsLocalRing R] (hR : ringKrullDim R = 1) {p : Ideal R} (hp : p ∈ minimalPrimes R) (φ : R →+* S)
    (hφ : Function.Surjective φ) (hker : RingHom.ker φ = p) : ringKrullDim S = 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ringKrullDim_eq_one_of_surjective_of_ker_mem_minimalPrimes» := P2M_GroundTheory_Heights__Heights_ringKrullDim_eq_one_of_surjective_of_ker_mem_minimalPrimes_db08cc59c2af
