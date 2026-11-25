-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_isCohenMacaulayLocalRing_of_minimalPrimes_sup_span_6892ec4f36ad
-- name    : P2M_GroundTheory_Heights__Heights_isCohenMacaulayLocalRing_of_minimalPrimes_sup_span_6892ec4f36ad
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T04:47:30.848792+00:00
-- url     : https://prove2.me/theorems/d9fea143-94cf-434c-aa38-8a6c1d19b03b
-- title:
--   P2 M Ground Theory Heights  Heights is Cohen Macaulay Local Ring of minimal Primes sup span 6892ec4f36ad: P2 M Ground Theory Heights  Heights is Cohen Macaulay Local Ring of minimal Primes sup span 68
-- statement:
--   The P2 M Ground Theory Heights  Heights is Cohen Macaulay Local Ring of minimal Primes sup span 6892ec4f36ad construction uses the P2 M Ground Theory Heights  Heights is Cohen Macaulay Local Ring of minimal Primes sup span 6892ec4f36ad property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PCMHeightOneGeneral.lean#L11-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PCMHeightOneGeneral.lean#L11-L78

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCMHeightOneGeneral
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCMLocusOpen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PSpecChartQuot
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCMHeightOneGeneral
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

theorem P2M_GroundTheory_Heights__Heights_isCohenMacaulayLocalRing_of_minimalPrimes_sup_span_6892ec4f36ad {R : Type*} [CommRing R] [IsNoetherianRing R]
    {J W : Ideal R} {g : R} [J.IsPrime] [W.IsPrime] (hg : g ∉ J)
    (hW : W ∈ (J ⊔ Ideal.span {g}).minimalPrimes) :
    IsCohenMacaulayLocalRing (Localization.AtPrime W ⧸ J.map (algebraMap R (Localization.AtPrime W))) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«isCohenMacaulayLocalRing_of_minimalPrimes_sup_span» := P2M_GroundTheory_Heights__Heights_isCohenMacaulayLocalRing_of_minimalPrimes_sup_span_6892ec4f36ad
