-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryMomentChannelStep_callArgs_cost
-- name    : ThreeSum.LightTernaryMomentChannelStep.callArgs_cost
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:49:42.442652+00:00
-- url     : https://prove2.me/theorems/61fd1068-d328-4f63-9108-f3ebff82560e
-- title:
--   Light Ternary Moment Channel Step: call Args cost
-- statement:
--   The Light Ternary Moment Channel Step construction uses the call Args cost property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryMomentChannelStep.lean#L27-L33
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryMomentChannelStep.lean#L27-L33

import Definitions.Def_Submission_ThreeSum_LightTernaryMomentChannels
import Definitions.Def_Submission_ThreeSum_LightTernaryMomentAccumulate
import Definitions.Def_Submission_ThreeSum_LightTernaryMomentChannelStep
set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryMomentChannelStep
open Light TernaryWeightChannels
set_option maxHeartbeats 1500000

theorem ThreeSum.LightTernaryMomentChannelStep.callArgs_cost (positions : List ℕ) :
    ((callArgs positions).map Expr.cost).sum=positions.length := by sorry
