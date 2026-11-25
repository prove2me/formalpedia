-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_isNilpotent_of_minimalPrimes_eq_singleton_06d31625bdb3
-- name    : P2M_GroundTheory_Heights__Heights_isNilpotent_of_minimalPrimes_eq_singleton_06d31625bdb3
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T04:52:28.53057+00:00
-- url     : https://prove2.me/theorems/77c4000d-d2cc-5789-a678-bbd53f09e8d9
-- title:
--   P2 M Ground Theory Heights  Heights is Nilpotent of minimal Primes eq singleton 06d31625bdb3: P2 M Ground Theory Heights  Heights is Nilpotent of minimal Primes eq singleton 06d31625bdb3
-- statement:
--   The P2 M Ground Theory Heights  Heights is Nilpotent of minimal Primes eq singleton 06d31625bdb3 construction uses the P2 M Ground Theory Heights  Heights is Nilpotent of minimal Primes eq singleton 06d31625bdb3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PLengthLocalizedQuotient.lean#L11-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PLengthLocalizedQuotient.lean#L11-L16

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLengthLocalizedQuotient
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLengthCutLocalizedModule
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PLocalizedQuotLength
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLengthLocalizedQuotient
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
universe u

theorem P2M_GroundTheory_Heights__Heights_isNilpotent_of_minimalPrimes_eq_singleton_06d31625bdb3 {B : Type*} [CommRing B] [IsNoetherianRing B] {P : Ideal B}
    (hmin : minimalPrimes B = {P}) : IsNilpotent P := by sorry

alias «GroundTheory».«Heights₂».«Heights».«isNilpotent_of_minimalPrimes_eq_singleton» := P2M_GroundTheory_Heights__Heights_isNilpotent_of_minimalPrimes_eq_singleton_06d31625bdb3
