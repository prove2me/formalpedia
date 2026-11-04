-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryMomentChannels_powerCircuit_bound
-- name    : ThreeSum.LightTernaryMomentChannels.powerCircuit_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:00:39.258197+00:00
-- url     : https://prove2.me/theorems/69ed2809-3d07-4707-9580-d0ebd44f0f66
-- title:
--   Light Ternary Moment Channels: power Circuit bound
-- statement:
--   The Light Ternary Moment Channels construction uses the power Circuit bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryMomentChannels.lean#L7-L11
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryMomentChannels.lean#L7-L11

import Definitions.Def_Submission_ThreeSum_LightTernaryScalarChannel
import Definitions.Def_Submission_ThreeSum_LightTernaryMomentChannels
set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryMomentChannels
open Light LightFixedArithmetic TernaryWeightChannels

theorem ThreeSum.LightTernaryMomentChannels.powerCircuit_bound (e : Circuit) (k : ℕ) (U : ℤ) :
    (powerCircuit e k).bound U=2*(e.bound U)^k := by sorry
