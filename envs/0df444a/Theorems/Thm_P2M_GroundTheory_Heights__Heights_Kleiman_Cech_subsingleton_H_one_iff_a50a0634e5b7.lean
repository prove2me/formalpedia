-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_Cech_subsingleton_H_one_iff_a50a0634e5b7
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_Cech_subsingleton_H_one_iff_a50a0634e5b7
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T06:21:22.896765+00:00
-- url     : https://prove2.me/theorems/b5de2c66-67db-4087-bf2e-e8afcffd115f
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Cech subsingleton H one iff a50a0634e5b7: P2 M Ground Theory Heights  Heights Kleiman Cech subsingleton H one iff a50a0634e5b7
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Cech subsingleton H one iff a50a0634e5b7 construction uses the P2 M Ground Theory Heights  Heights Kleiman Cech subsingleton H one iff a50a0634e5b7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PClaimVanishCech.lean#L18-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PClaimVanishCech.lean#L18-L26

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
open GroundTheory.Heights₂.Heights.Kleiman.Cech
variable {n : ℕ} {U : Finset (Fin n)} {R : Type u} [CommRing R] {G : Cell U → Type v}
  [∀ I, AddCommGroup (G I)] [∀ I, Module R (G I)] {ρ : ∀ I J : Cell U, I.1 ⊆ J.1 → G I →ₗ[R] G J}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_Cech_subsingleton_H_one_iff_a50a0634e5b7 :
    Subsingleton (H G ρ 1) ↔ ∀ z : Cochain G 1, d G ρ 1 z = 0 → ∃ w : Cochain G 0, d G ρ 0 w = z := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«Cech».«subsingleton_H_one_iff» := P2M_GroundTheory_Heights__Heights_Kleiman_Cech_subsingleton_H_one_iff_a50a0634e5b7
