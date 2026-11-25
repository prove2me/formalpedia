-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_TopDualBound_grassConst_lines_9d63eb767f82
-- name    : P2M_GroundTheory_Heights__Heights_TopDualBound_grassConst_lines_9d63eb767f82
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:41:05.100562+00:00
-- url     : https://prove2.me/theorems/07d8688e-2856-4740-bd9f-f845879e7355
-- title:
--   P2 M Ground Theory Heights  Heights Top Dual Bound grass Const lines 9d63eb767f82: P2 M Ground Theory Heights  Heights Top Dual Bound grass Const lines 9d63eb767f82
-- statement:
--   The P2 M Ground Theory Heights  Heights Top Dual Bound grass Const lines 9d63eb767f82 construction uses the P2 M Ground Theory Heights  Heights Top Dual Bound grass Const lines 9d63eb767f82 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualTopBound.lean#L12-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualTopBound.lean#L12-L16

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLineDegreeDual
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ScaledExample
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualTopBound
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
open ReciprocityTheory.ChartRestriction.G.Geo
open GroundTheory.Heights₂.Heights.TopDualBound

theorem P2M_GroundTheory_Heights__Heights_TopDualBound_grassConst_lines_9d63eb767f82 {i : ℕ} (hi : 1 ≤ i) : grassConst 1 1 (i - 1) = 1 / 2 * Real.log i := by sorry

alias «GroundTheory».«Heights₂».«Heights».«TopDualBound».«grassConst_lines» := P2M_GroundTheory_Heights__Heights_TopDualBound_grassConst_lines_9d63eb767f82
