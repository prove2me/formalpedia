-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_Cech_d_one_d_zero_613304503aca
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_Cech_d_one_d_zero_613304503aca
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T06:21:54.211805+00:00
-- url     : https://prove2.me/theorems/24545abf-b596-4735-91a7-d0806aa116e1
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Cech d one d zero 613304503aca: P2 M Ground Theory Heights  Heights Kleiman Cech d one d zero 613304503aca
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Cech d one d zero 613304503aca construction uses the P2 M Ground Theory Heights  Heights Kleiman Cech d one d zero 613304503aca property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PClaimVanishCech.lean#L47-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PClaimVanishCech.lean#L47-L74

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_Cech_d_one_d_zero_613304503aca
    (hρ : ∀ (I J K : Cell U) (h : I.1 ⊆ J.1) (h' : J.1 ⊆ K.1) (m : G I),
      ρ J K h' (ρ I J h m) = ρ I K (h.trans h') m)
    (w : Cochain G 0) : d G ρ 1 (d G ρ 0 w) = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«Cech».«d_one_d_zero» := P2M_GroundTheory_Heights__Heights_Kleiman_Cech_d_one_d_zero_613304503aca
