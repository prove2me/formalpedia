-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_KLinesCoordDet_det_eq_89a8912c4c84
-- name    : P2M_GroundTheory_Heights__Heights_KLinesCoordDet_det_eq_89a8912c4c84
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:26:31.156004+00:00
-- url     : https://prove2.me/theorems/5c6da612-26b1-4a21-b597-a70d2dd8011c
-- title:
--   P2 M Ground Theory Heights  Heights KLines Coord Det det eq 89a8912c4c84: P2 M Ground Theory Heights  Heights KLines Coord Det det eq 89a8912c4c84
-- statement:
--   The P2 M Ground Theory Heights  Heights KLines Coord Det det eq 89a8912c4c84 construction uses the P2 M Ground Theory Heights  Heights KLines Coord Det det eq 89a8912c4c84 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PLinesCoordDet.lean#L29-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PLinesCoordDet.lean#L29-L35

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

theorem P2M_GroundTheory_Heights__Heights_KLinesCoordDet_det_eq_89a8912c4c84 (hb : ∀ i, B (Sum.inl i) = b i) :
    (B.toMatrix (Sum.elim b c)).det = (B.toMatrix (Sum.elim b c)).toBlocks₂₂.det := by sorry

alias «GroundTheory».«Heights₂».«Heights».«KLinesCoordDet».«det_eq» := P2M_GroundTheory_Heights__Heights_KLinesCoordDet_det_eq_89a8912c4c84
