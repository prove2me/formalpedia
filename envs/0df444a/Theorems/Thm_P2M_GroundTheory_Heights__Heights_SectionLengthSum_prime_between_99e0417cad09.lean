-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SectionLengthSum_prime_between_99e0417cad09
-- name    : P2M_GroundTheory_Heights__Heights_SectionLengthSum_prime_between_99e0417cad09
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T04:37:13.492546+00:00
-- url     : https://prove2.me/theorems/675df559-c1ac-4798-923a-51e421a85c50
-- title:
--   P2 M Ground Theory Heights  Heights Section Length Sum prime between 99e0417cad09: P2 M Ground Theory Heights  Heights Section Length Sum prime between 99e0417cad09
-- statement:
--   The P2 M Ground Theory Heights  Heights Section Length Sum prime between 99e0417cad09 construction uses the P2 M Ground Theory Heights  Heights Section Length Sum prime between 99e0417cad09 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PSectionLengthSum.lean#L10-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PSectionLengthSum.lean#L10-L46

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

theorem P2M_GroundTheory_Heights__Heights_SectionLengthSum_prime_between_99e0417cad09 {A : Type*} [CommRing A] [IsNoetherianRing A] {J W Q : Ideal A} {f : A}
    (hWP : ∀ P ∈ J.minimalPrimes, P ≤ W → W ∈ (P ⊔ Ideal.span {f}).minimalPrimes)
    [hQ : Q.IsPrime] (hJQ : J ≤ Q) (hQW : Q ≤ W) : Q ∈ J.minimalPrimes ∨ Q = W := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SectionLengthSum».«prime_between» := P2M_GroundTheory_Heights__Heights_SectionLengthSum_prime_between_99e0417cad09
