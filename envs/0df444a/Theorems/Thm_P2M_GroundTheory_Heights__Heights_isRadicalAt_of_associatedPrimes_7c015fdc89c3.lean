-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_isRadicalAt_of_associatedPrimes_7c015fdc89c3
-- name    : P2M_GroundTheory_Heights__Heights_isRadicalAt_of_associatedPrimes_7c015fdc89c3
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T04:47:40.065218+00:00
-- url     : https://prove2.me/theorems/cbfce254-94ec-4259-b9bf-83f0413a22a8
-- title:
--   P2 M Ground Theory Heights  Heights is Radical At of associated Primes 7c015fdc89c3: P2 M Ground Theory Heights  Heights is Radical At of associated Primes 7c015fdc89c3
-- statement:
--   The P2 M Ground Theory Heights  Heights is Radical At of associated Primes 7c015fdc89c3 construction uses the P2 M Ground Theory Heights  Heights is Radical At of associated Primes 7c015fdc89c3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSliceReducedGeneral.lean#L11-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSliceReducedGeneral.lean#L11-L39

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceReducedGeneral
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceUnmixedGeneral
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceReducedAway
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSliceReducedGeneral
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
open MvPolynomial Matrix ComplexSets

theorem P2M_GroundTheory_Heights__Heights_isRadicalAt_of_associatedPrimes_7c015fdc89c3 {n : ℕ} {I : Ideal (MvPolynomial (Fin n) ℂ)} {q : Fin n → ℂ}
    (hA : ∀ P ∈ associatedPrimes (MvPolynomial (Fin n) ℂ) (MvPolynomial (Fin n) ℂ ⧸ I),
      P ≤ RingHom.ker (eval q) → P ∈ I.minimalPrimes ∧ P ≠ RingHom.ker (eval q))
    (hB : ∀ P : Ideal (MvPolynomial (Fin n) ℂ), P.IsPrime → I ≤ P → P ≠ RingHom.ker (eval q) →
      ∀ g ∈ I.radical, ∃ s ∉ P, s * g ∈ I) :
    IsRadicalAt I q := by sorry

alias «GroundTheory».«Heights₂».«Heights».«isRadicalAt_of_associatedPrimes» := P2M_GroundTheory_Heights__Heights_isRadicalAt_of_associatedPrimes_7c015fdc89c3
