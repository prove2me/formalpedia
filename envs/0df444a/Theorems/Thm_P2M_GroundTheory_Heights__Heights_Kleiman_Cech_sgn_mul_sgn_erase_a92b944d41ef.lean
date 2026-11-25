-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_Cech_sgn_mul_sgn_erase_a92b944d41ef
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_Cech_sgn_mul_sgn_erase_a92b944d41ef
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T07:53:02.945576+00:00
-- url     : https://prove2.me/theorems/164f39be-d0e2-462f-9095-293b9211cab5
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Cech sgn mul sgn erase a92b944d41ef: P2 M Ground Theory Heights  Heights Kleiman Cech sgn mul sgn erase a92b944d41ef
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Cech sgn mul sgn erase a92b944d41ef construction uses the P2 M Ground Theory Heights  Heights Kleiman Cech sgn mul sgn erase a92b944d41ef property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PClaimVanishCech.lean#L28-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PClaimVanishCech.lean#L28-L45

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_Cech_sgn_mul_sgn_erase_a92b944d41ef {J : Finset (Fin n)} {j k : Fin n} (hj : j ∈ J) (hk : k ∈ J) (hjk : j ≠ k) :
    sgn J j * sgn (J.erase j) k = -(sgn J k * sgn (J.erase k) j) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«Cech».«sgn_mul_sgn_erase» := P2M_GroundTheory_Heights__Heights_Kleiman_Cech_sgn_mul_sgn_erase_a92b944d41ef
