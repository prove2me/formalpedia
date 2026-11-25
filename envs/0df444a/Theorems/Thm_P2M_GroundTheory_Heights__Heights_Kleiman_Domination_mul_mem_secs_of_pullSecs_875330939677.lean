-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_Domination_mul_mem_secs_of_pullSecs_875330939677
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_Domination_mul_mem_secs_of_pullSecs_875330939677
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T06:21:43.56411+00:00
-- url     : https://prove2.me/theorems/08f49ed7-d49c-4984-a5fd-401d93ef0bf1
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Domination mul mem secs of pull Secs 875330939677: P2 M Ground Theory Heights  Heights Kleiman Domination mul mem secs of pull Secs 875330939677
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Domination mul mem secs of pull Secs 875330939677 construction uses the P2 M Ground Theory Heights  Heights Kleiman Domination mul mem secs of pull Secs 875330939677 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PDomination.lean#L294-L315
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PDomination.lean#L294-L315

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PDomination
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
universe u w
open GroundTheory.Heights₂.Heights.Kleiman.Domination
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N N' : ℕ}
  {x : Fin (N + 1) → Ω} {x' : Fin (N' + 1) → Ω}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_Domination_mul_mem_secs_of_pullSecs_875330939677 {L L' : SubSystem S x Ω} {κ : Ω}
    (h : ∀ (i : Fin (N + 1)) (hi : x i ≠ 0), ∀ b ∈ domRing S x x' i, ∀ l ∈ L.sub (singleChart hi),
      κ * (b * l) ∈ L'.sub (singleChart hi)) :
    ∀ z ∈ pullSecs x' L, κ * z ∈ L'.secs := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«Domination».«mul_mem_secs_of_pullSecs» := P2M_GroundTheory_Heights__Heights_Kleiman_Domination_mul_mem_secs_of_pullSecs_875330939677
