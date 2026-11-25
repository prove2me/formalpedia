-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_Domination_ne_zero_of_isBirationalPt_026f5142f832
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_Domination_ne_zero_of_isBirationalPt_026f5142f832
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T06:21:31.510485+00:00
-- url     : https://prove2.me/theorems/064126ea-1873-54b3-8e86-c300f3b8f2b9
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Domination ne zero of is Birational Pt 026f5142f832: P2 M Ground Theory Heights  Heights Kleiman Domination ne zero of is Birational Pt 026f5142f832
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Domination ne zero of is Birational Pt 026f5142f832 construction uses the P2 M Ground Theory Heights  Heights Kleiman Domination ne zero of is Birational Pt 026f5142f832 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PDomination.lean#L319-L324
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PDomination.lean#L319-L324

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
omit [Algebra S Ω]

theorem P2M_GroundTheory_Heights__Heights_Kleiman_Domination_ne_zero_of_isBirationalPt_026f5142f832 [Algebra S Ω] {y : Fin (N' + 1) → Ω} (h : IsBirationalPt S y) :
    y ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«Domination».«ne_zero_of_isBirationalPt» := P2M_GroundTheory_Heights__Heights_Kleiman_Domination_ne_zero_of_isBirationalPt_026f5142f832
