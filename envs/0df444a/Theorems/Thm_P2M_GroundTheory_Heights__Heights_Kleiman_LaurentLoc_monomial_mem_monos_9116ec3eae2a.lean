-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_LaurentLoc_monomial_mem_monos_9116ec3eae2a
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_LaurentLoc_monomial_mem_monos_9116ec3eae2a
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:27:21.884826+00:00
-- url     : https://prove2.me/theorems/df1f0ce1-bbf3-4f2c-b2ec-220bc70d3584
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Laurent Loc monomial mem monos 9116ec3eae2a: P2 M Ground Theory Heights  Heights Kleiman Laurent Loc monomial mem monos 9116ec3eae2a
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Laurent Loc monomial mem monos 9116ec3eae2a construction uses the P2 M Ground Theory Heights  Heights Kleiman Laurent Loc monomial mem monos 9116ec3eae2a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSerrePolyLaurent.lean#L65-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSerrePolyLaurent.lean#L65-L70

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsSerrePoly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSerrePolyLaurent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u
open GroundTheory.Heights₂.Heights.Kleiman.LaurentLoc
variable (S : Type u) [CommRing S] (N : ℕ)
variable {S N}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_LaurentLoc_monomial_mem_monos_9116ec3eae2a {I : Finset (Fin (N + 1))} (f : Fin (N + 1) →₀ ℕ) (hf : ∀ j ∉ I, f j = 0) :
    (monomial f 1 : Poly S N) ∈ monos I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«LaurentLoc».«monomial_mem_monos» := P2M_GroundTheory_Heights__Heights_Kleiman_LaurentLoc_monomial_mem_monos_9116ec3eae2a
