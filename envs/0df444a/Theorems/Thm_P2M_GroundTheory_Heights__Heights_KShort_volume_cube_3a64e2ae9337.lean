-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_KShort_volume_cube_3a64e2ae9337
-- name    : P2M_GroundTheory_Heights__Heights_KShort_volume_cube_3a64e2ae9337
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:26:25.35841+00:00
-- url     : https://prove2.me/theorems/6484a152-9e11-40f7-bace-53b3c7d67c32
-- title:
--   P2 M Ground Theory Heights  Heights KShort volume cube 3a64e2ae9337: P2 M Ground Theory Heights  Heights KShort volume cube 3a64e2ae9337
-- statement:
--   The P2 M Ground Theory Heights  Heights KShort volume cube 3a64e2ae9337 construction uses the P2 M Ground Theory Heights  Heights KShort volume cube 3a64e2ae9337 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/ShortVectors.lean#L19-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/ShortVectors.lean#L19-L25

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KernelsMatrix
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ShortVectors
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
open MeasureTheory Module Metric
noncomputable section
open GroundTheory.Heights₂.Heights.KShort

theorem P2M_GroundTheory_Heights__Heights_KShort_volume_cube_3a64e2ae9337 (n : ℕ) {c : ℝ} (hc : 0 ≤ c) :
    volume (cube n c) = ENNReal.ofReal ((2 * c) ^ n) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«KShort».«volume_cube» := P2M_GroundTheory_Heights__Heights_KShort_volume_cube_3a64e2ae9337
