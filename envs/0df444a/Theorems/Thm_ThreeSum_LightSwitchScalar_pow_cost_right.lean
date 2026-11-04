-- Prove2me | Theorems.Thm_ThreeSum_LightSwitchScalar_pow_cost_right
-- name    : ThreeSum.LightSwitchScalar.pow_cost_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:35:33.837609+00:00
-- url     : https://prove2.me/theorems/a27a7e62-2f84-4aff-b5f8-35b499570ad1
-- title:
--   Light Switch Scalar: pow cost right
-- statement:
--   The Light Switch Scalar construction uses the pow cost right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSwitchScalar.lean#L20-L21
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSwitchScalar.lean#L20-L21

import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Logs
import Definitions.Def_Submission_ThreeSum_LightSwitchScalar
set_option autoImplicit false
open ThreeSum ThreeSum.LightSwitchScalar
open Light
set_option maxHeartbeats 1600000

theorem ThreeSum.LightSwitchScalar.pow_cost_right (B a b : ℕ) (hB : 1 ≤ B) : B^b ≤ B^(a+b+1) := by sorry
