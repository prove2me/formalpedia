-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_KCoord_mul_log_le_eb577467598a
-- name    : P2M_GroundTheory_Heights__Heights_KCoord_mul_log_le_eb577467598a
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:25:32.702854+00:00
-- url     : https://prove2.me/theorems/63b789dd-5c2f-451d-9d4c-fbc70f4b133f
-- title:
--   P2 M Ground Theory Heights  Heights KCoord mul log le eb577467598a: P2 M Ground Theory Heights  Heights KCoord mul log le eb577467598a
-- statement:
--   The P2 M Ground Theory Heights  Heights KCoord mul log le eb577467598a construction uses the P2 M Ground Theory Heights  Heights KCoord mul log le eb577467598a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/CoordWeak.lean#L37-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/CoordWeak.lean#L37-L48

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

theorem P2M_GroundTheory_Heights__Heights_KCoord_mul_log_le_eb577467598a (G a : ℝ) (hG : 0 ≤ G) (ha : 0 < a) :
    G * log (1 + a) ≤ π / 192 * a ^ 2 + 48 / π * G ^ 2 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«KCoord».«mul_log_le» := P2M_GroundTheory_Heights__Heights_KCoord_mul_log_le_eb577467598a
