-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SubSystem_subsingleton_H_one_of_smul_53085ae11a31
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_SubSystem_subsingleton_H_one_of_smul_53085ae11a31
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T06:23:07.761001+00:00
-- url     : https://prove2.me/theorems/6fd0eba4-f067-4ee1-ae00-d44ad0c25dce
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Sub System subsingleton H one of smul 53085ae11a31: P2 M Ground Theory Heights  Heights Kleiman Sub System subsingleton H one of smul 53085ae11a31
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Sub System subsingleton H one of smul 53085ae11a31 construction uses the P2 M Ground Theory Heights  Heights Kleiman Sub System subsingleton H one of smul 53085ae11a31 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PClaimVanishCech.lean#L134-L166
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PClaimVanishCech.lean#L134-L166

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_SubSystem_subsingleton_H_one_of_smul_53085ae11a31 (F' G : SubSystem S x Ω) (σ : Ω) (hσ : σ ≠ 0)
    (hG : ∀ I z, z ∈ G.sub I ↔ ∃ y ∈ F'.sub I, z = σ * y) (hF : Subsingleton (F'.H 1)) :
    Subsingleton (G.H 1) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«SubSystem».«subsingleton_H_one_of_smul» := P2M_GroundTheory_Heights__Heights_Kleiman_SubSystem_subsingleton_H_one_of_smul_53085ae11a31
