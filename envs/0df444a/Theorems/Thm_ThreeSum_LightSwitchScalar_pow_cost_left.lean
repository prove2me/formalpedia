-- Prove2me | Theorems.Thm_ThreeSum_LightSwitchScalar_pow_cost_left
-- name    : ThreeSum.LightSwitchScalar.pow_cost_left
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:35:44.670186+00:00
-- url     : https://prove2.me/theorems/e12324b9-2978-41c9-852d-57fb2b24b77b
-- title:
--   Light Switch Scalar: pow cost left
-- statement:
--   The Light Switch Scalar construction uses the pow cost left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSwitchScalar.lean#L17-L18
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSwitchScalar.lean#L17-L18

import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Logs
import Definitions.Def_Submission_ThreeSum_LightSwitchScalar
set_option autoImplicit false
open ThreeSum ThreeSum.LightSwitchScalar
open Light
set_option maxHeartbeats 1600000

theorem ThreeSum.LightSwitchScalar.pow_cost_left (B a b : ℕ) (hB : 1 ≤ B) : B^a ≤ B^(a+b+1) := by sorry
