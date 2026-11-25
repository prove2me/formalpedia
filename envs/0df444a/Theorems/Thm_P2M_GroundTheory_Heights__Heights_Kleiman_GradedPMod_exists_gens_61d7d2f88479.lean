-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_GradedPMod_exists_gens_61d7d2f88479
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_GradedPMod_exists_gens_61d7d2f88479
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:30:18.486456+00:00
-- url     : https://prove2.me/theorems/07aeb645-9f0c-42dd-b1a3-e167799fc077
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Graded PMod exists gens 61d7d2f88479: P2 M Ground Theory Heights  Heights Kleiman Graded PMod exists gens 61d7d2f88479
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Graded PMod exists gens 61d7d2f88479 construction uses the P2 M Ground Theory Heights  Heights Kleiman Graded PMod exists gens 61d7d2f88479 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSerreOnto.lean#L174-L189
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSerreOnto.lean#L174-L189

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSerreOnto
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
universe u v w w'
variable {S : Type u} [CommRing S] {N : ℕ}
variable {M : Type v} [AddCommGroup M] [Module (Poly S N) M] [Module S M] [IsScalarTower S (Poly S N) M]
omit [IsScalarTower S (Poly S N) M]

theorem P2M_GroundTheory_Heights__Heights_Kleiman_GradedPMod_exists_gens_61d7d2f88479 (𝓜 : GradedPMod S N M) (hM : Module.Finite (Poly S N) M) :
    ∃ (r : ℕ) (g : Fin r → M) (deg : Fin r → ℤ), (∀ j, g j ∈ 𝓜.piece (deg j)) ∧
      Submodule.span (Poly S N) (Set.range g) = ⊤ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«GradedPMod».«exists_gens» := P2M_GroundTheory_Heights__Heights_Kleiman_GradedPMod_exists_gens_61d7d2f88479
