-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_MinkowskiCount_cube_le_unitBallVolume_6eea6a272945
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_MinkowskiCount_cube_le_unitBallVolume_6eea6a272945
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:18:52.607654+00:00
-- url     : https://prove2.me/theorems/42c5bdaa-c22e-5b47-99be-8a2c5244949c
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Minkowski Count cube le unit Ball Volume 6eea6a272945: P2 M Ground Theory Heights  Heights Hilbert Samuel Minkowski Count cube le unit Ball Volume 6e
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Minkowski Count cube le unit Ball Volume 6eea6a272945 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Minkowski Count cube le unit Ball Volume 6eea6a272945 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PMinkowskiCount.lean#L117-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PMinkowskiCount.lean#L117-L145

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsLattice
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PMinkowskiCount
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MeasureTheory Module Metric
open scoped ENNReal
noncomputable section
open GroundTheory.Heights₂.Heights.HilbertSamuel.MinkowskiCount

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_MinkowskiCount_cube_le_unitBallVolume_6eea6a272945 (R : ℕ) : (2 / Real.sqrt R) ^ R ≤ unitBallVolume R := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«MinkowskiCount».«cube_le_unitBallVolume» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_MinkowskiCount_cube_le_unitBallVolume_6eea6a272945
