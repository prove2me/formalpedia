-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_KCoord_posLog_le_half_log_fc664a0a4135
-- name    : P2M_GroundTheory_Heights__Heights_KCoord_posLog_le_half_log_fc664a0a4135
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:27:12.237174+00:00
-- url     : https://prove2.me/theorems/5981eb2f-56e7-425e-9d92-e4f4625378e0
-- title:
--   P2 M Ground Theory Heights  Heights KCoord pos Log le half log fc664a0a4135: P2 M Ground Theory Heights  Heights KCoord pos Log le half log fc664a0a4135
-- statement:
--   The P2 M Ground Theory Heights  Heights KCoord pos Log le half log fc664a0a4135 construction uses the P2 M Ground Theory Heights  Heights KCoord pos Log le half log fc664a0a4135 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/CoordWeak.lean#L50-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/CoordWeak.lean#L50-L68

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KernelsMatrix
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_CoordWeak
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
open Real
open GroundTheory.Heights₂.Heights.KCoord

theorem P2M_GroundTheory_Heights__Heights_KCoord_posLog_le_half_log_fc664a0a4135 (ρ : ℝ) (hρ : 0 < ρ) :
    posLog (1 / ρ) ≤ 1 / 2 * log (1 + (ρ ^ 2)⁻¹) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«KCoord».«posLog_le_half_log» := P2M_GroundTheory_Heights__Heights_KCoord_posLog_le_half_log_fc664a0a4135
