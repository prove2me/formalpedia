-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_KLinesCoordDet_toBlocks___eq_1b8652055f7a
-- name    : P2M_GroundTheory_Heights__Heights_KLinesCoordDet_toBlocks___eq_1b8652055f7a
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:26:20.567401+00:00
-- url     : https://prove2.me/theorems/f2111b77-d229-4da0-83c5-f275f9e0b2a6
-- title:
--   P2 M Ground Theory Heights  Heights KLines Coord Det to Blocks   eq 1b8652055f7a: P2 M Ground Theory Heights  Heights KLines Coord Det to Blocks   eq 1b8652055f7a
-- statement:
--   The P2 M Ground Theory Heights  Heights KLines Coord Det to Blocks   eq 1b8652055f7a construction uses the P2 M Ground Theory Heights  Heights KLines Coord Det to Blocks   eq 1b8652055f7a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PLinesCoordDet.lean#L23-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PLinesCoordDet.lean#L23-L27

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLines
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PLinesCoordDet
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open Matrix
open GroundTheory.Heights₂.Heights.KLinesCoordDet
variable {K : Type} [Field K] {n m k : ℕ} (B : Module.Basis (Fin m ⊕ Fin k) K (Fin n → K))
  (b : Fin m → Fin n → K) (c : Fin k → Fin n → K)

theorem P2M_GroundTheory_Heights__Heights_KLinesCoordDet_toBlocks___eq_1b8652055f7a (hb : ∀ i, B (Sum.inl i) = b i) :
    (B.toMatrix (Sum.elim b c)).toBlocks₂₁ = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«KLinesCoordDet».«toBlocks₂₁_eq» := P2M_GroundTheory_Heights__Heights_KLinesCoordDet_toBlocks___eq_1b8652055f7a
