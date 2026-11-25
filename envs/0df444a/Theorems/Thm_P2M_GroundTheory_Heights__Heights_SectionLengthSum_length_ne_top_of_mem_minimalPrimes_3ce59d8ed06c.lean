-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SectionLengthSum_length_ne_top_of_mem_minimalPrimes_3ce59d8ed06c
-- name    : P2M_GroundTheory_Heights__Heights_SectionLengthSum_length_ne_top_of_mem_minimalPrimes_3ce59d8ed06c
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T04:37:09.653595+00:00
-- url     : https://prove2.me/theorems/6ce5d010-44f1-48dc-a1f9-24c8a1cf47f5
-- title:
--   P2 M Ground Theory Heights  Heights Section Length Sum length ne top of mem minimal Primes 3ce59d8ed06c: P2 M Ground Theory Heights  Heights Section Length Sum length ne top of mem minimal Primes 3ce5
-- statement:
--   The P2 M Ground Theory Heights  Heights Section Length Sum length ne top of mem minimal Primes 3ce59d8ed06c construction uses the P2 M Ground Theory Heights  Heights Section Length Sum length ne top of mem minimal Primes 3ce59d8ed06c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PSectionLengthSum.lean#L48-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PSectionLengthSum.lean#L48-L52

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsSectionLengthSum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsLocalSectionLengthSum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PSectionLengthSum
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
open GroundTheory.Heights₂.Heights.SectionLengthSum

theorem P2M_GroundTheory_Heights__Heights_SectionLengthSum_length_ne_top_of_mem_minimalPrimes_3ce59d8ed06c {B : Type*} [CommRing B] [IsNoetherianRing B] [IsLocalRing B]
    (I : Ideal B) (hI : IsLocalRing.maximalIdeal B ∈ I.minimalPrimes) : Module.length B (B ⧸ I) ≠ ⊤ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SectionLengthSum».«length_ne_top_of_mem_minimalPrimes» := P2M_GroundTheory_Heights__Heights_SectionLengthSum_length_ne_top_of_mem_minimalPrimes_3ce59d8ed06c
