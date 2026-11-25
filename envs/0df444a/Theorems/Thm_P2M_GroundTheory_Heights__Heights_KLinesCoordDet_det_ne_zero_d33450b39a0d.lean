-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_KLinesCoordDet_det_ne_zero_d33450b39a0d
-- name    : P2M_GroundTheory_Heights__Heights_KLinesCoordDet_det_ne_zero_d33450b39a0d
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:25:58.847076+00:00
-- url     : https://prove2.me/theorems/58ddbfcb-a3f8-4a70-abed-0b08fa1348d1
-- title:
--   P2 M Ground Theory Heights  Heights KLines Coord Det det ne zero d33450b39a0d: P2 M Ground Theory Heights  Heights KLines Coord Det det ne zero d33450b39a0d
-- statement:
--   The P2 M Ground Theory Heights  Heights KLines Coord Det det ne zero d33450b39a0d construction uses the P2 M Ground Theory Heights  Heights KLines Coord Det det ne zero d33450b39a0d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PLinesCoordDet.lean#L37-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PLinesCoordDet.lean#L37-L46

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

theorem P2M_GroundTheory_Heights__Heights_KLinesCoordDet_det_ne_zero_d33450b39a0d (hli : LinearIndependent K (Sum.elim b c)) :
    (B.toMatrix (Sum.elim b c)).det ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«KLinesCoordDet».«det_ne_zero» := P2M_GroundTheory_Heights__Heights_KLinesCoordDet_det_ne_zero_d33450b39a0d
