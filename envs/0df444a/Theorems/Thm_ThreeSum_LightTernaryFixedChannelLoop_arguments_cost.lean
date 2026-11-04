-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryFixedChannelLoop_arguments_cost
-- name    : ThreeSum.LightTernaryFixedChannelLoop.arguments_cost
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:52:41.021876+00:00
-- url     : https://prove2.me/theorems/b390baff-1229-4cea-90ac-ced853fc6b02
-- title:
--   Light Ternary Fixed Channel Loop: arguments cost
-- statement:
--   The Light Ternary Fixed Channel Loop construction uses the arguments cost property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryFixedChannelLoop.lean#L36-L38
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryFixedChannelLoop.lean#L36-L38

import Definitions.Def_Submission_ThreeSum_LightTernaryMomentChannelStep
import Definitions.Def_Submission_ThreeSum_TernaryMomentSchedule
import Definitions.Def_Submission_ThreeSum_LightTernaryFixedChannelLoop
set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryFixedChannelLoop
open Light
set_option maxHeartbeats 1500000

theorem ThreeSum.LightTernaryFixedChannelLoop.arguments_cost (arity : ℕ) :
    ((arguments arity).map Expr.cost).sum=arity := by sorry
