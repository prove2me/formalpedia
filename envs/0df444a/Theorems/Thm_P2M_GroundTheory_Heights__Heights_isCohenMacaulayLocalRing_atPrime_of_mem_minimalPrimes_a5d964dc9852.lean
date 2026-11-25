-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_isCohenMacaulayLocalRing_atPrime_of_mem_minimalPrimes_a5d964dc9852
-- name    : P2M_GroundTheory_Heights__Heights_isCohenMacaulayLocalRing_atPrime_of_mem_minimalPrimes_a5d964dc9852
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T04:47:55.909751+00:00
-- url     : https://prove2.me/theorems/ee3ec00a-fa4f-48ce-9491-7850818d3213
-- title:
--   P2 M Ground Theory Heights  Heights is Cohen Macaulay Local Ring at Prime of mem minimal Primes a5d964dc9852: P2 M Ground Theory Heights  Heights is Cohen Macaulay Local Ring at Prime of mem minimal P
-- statement:
--   The P2 M Ground Theory Heights  Heights is Cohen Macaulay Local Ring at Prime of mem minimal Primes a5d964dc9852 construction uses the P2 M Ground Theory Heights  Heights is Cohen Macaulay Local Ring at Prime of mem minimal Primes a5d964dc9852 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PCMGeneralPoint.lean#L10-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PCMGeneralPoint.lean#L10-L42

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCMGeneralPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCMLocusOpen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCMGeneralPoint
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
open MvPolynomial ComplexSets IsLocalRing

theorem P2M_GroundTheory_Heights__Heights_isCohenMacaulayLocalRing_atPrime_of_mem_minimalPrimes_a5d964dc9852 {n : ℕ}
    {I W : Ideal (MvPolynomial (Fin n) ℂ)} [W.IsPrime] (hW : W ∈ I.minimalPrimes) :
    IsCohenMacaulayLocalRing (Localization.AtPrime W ⧸
      I.map (algebraMap (MvPolynomial (Fin n) ℂ) (Localization.AtPrime W))) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«isCohenMacaulayLocalRing_atPrime_of_mem_minimalPrimes» := P2M_GroundTheory_Heights__Heights_isCohenMacaulayLocalRing_atPrime_of_mem_minimalPrimes_a5d964dc9852
