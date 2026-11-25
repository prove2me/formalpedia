-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_freeCoordinate_toH0_00580c569653
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_freeCoordinate_toH0_00580c569653
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:42:34.592725+00:00
-- url     : https://prove2.me/theorems/c1d468a7-5717-55b6-b3ab-871474d1cc54
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman free Coordinate to H0 00580c569653: P2 M Ground Theory Heights  Heights Kleiman free Coordinate to H0 00580c569653
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman free Coordinate to H0 00580c569653 construction uses the P2 M Ground Theory Heights  Heights Kleiman free Coordinate to H0 00580c569653 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSerreFree.lean#L212-L219
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSerreFree.lean#L212-L219

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSerreFree
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
variable {S : Type u} [CommRing S] {N : ℕ}
variable {M : Type v} [AddCommGroup M] [Module (Poly S N) M] [Module S M]
  [IsScalarTower S (Poly S N) M]
variable {M' : Type w} [AddCommGroup M'] [Module (Poly S N) M'] [Module S M']
  [IsScalarTower S (Poly S N) M']
variable (𝓜 : GradedPMod S N M) {r : ℕ} (b : Module.Basis (Fin r) (Poly S N) M) (d : Fin r → ℤ)
variable (hb : ∀ j, b j ∈ 𝓜.piece (d j))
include hb

theorem P2M_GroundTheory_Heights__Heights_Kleiman_freeCoordinate_toH0_00580c569653 (c : ℤ) (j : Fin r) (m : 𝓜.piece c) :
    freeCoord 𝓜 b d hb 0 c j (toH0 𝓜 c m) =
      toH0 (polyGraded S N) (c - d j) ⟨b.coord j m, coord_mem_piece 𝓜 b d hb m.2 j⟩ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«freeCoordinate_toH0» := P2M_GroundTheory_Heights__Heights_Kleiman_freeCoordinate_toH0_00580c569653
