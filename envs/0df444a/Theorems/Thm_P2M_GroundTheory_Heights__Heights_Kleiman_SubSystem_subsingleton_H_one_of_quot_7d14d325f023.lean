-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SubSystem_subsingleton_H_one_of_quot_7d14d325f023
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_SubSystem_subsingleton_H_one_of_quot_7d14d325f023
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T06:24:50.222826+00:00
-- url     : https://prove2.me/theorems/9e8e3bab-4324-42f7-8131-350609385689
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Sub System subsingleton H one of quot 7d14d325f023: P2 M Ground Theory Heights  Heights Kleiman Sub System subsingleton H one of quot 7d14d325f023
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Sub System subsingleton H one of quot 7d14d325f023 construction uses the P2 M Ground Theory Heights  Heights Kleiman Sub System subsingleton H one of quot 7d14d325f023 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PClaimVanishCech.lean#L93-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PClaimVanishCech.lean#L93-L130

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PClaimVanishCech
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
universe u v w
open GroundTheory.Heights₂.Heights.Kleiman.SubSystem
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}
variable {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
set_option maxHeartbeats 1000000

theorem P2M_GroundTheory_Heights__Heights_Kleiman_SubSystem_subsingleton_H_one_of_quot_7d14d325f023 (F G : SubSystem S x E)
    (hGF : ∀ I, ∀ y ∈ G.sub I, y ∈ F.sub I) (hG : Subsingleton (G.H 1))
    (hQ : Subsingleton (quotH F G 1)) : Subsingleton (F.H 1) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«SubSystem».«subsingleton_H_one_of_quot» := P2M_GroundTheory_Heights__Heights_Kleiman_SubSystem_subsingleton_H_one_of_quot_7d14d325f023
