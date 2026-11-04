-- Prove2me | Theorems.Thm_ThreeSum_LightOutputDecodeDivide_time_le_budget
-- name    : ThreeSum.LightOutputDecodeDivide.time_le_budget
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:39:23.946607+00:00
-- url     : https://prove2.me/theorems/35d425d4-4705-49a1-9a43-086326470cb0
-- title:
--   Light Output Decode Divide: time le budget
-- statement:
--   The Light Output Decode Divide construction uses the time le budget property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightOutputDecodeDivide.lean#L118-L121
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightOutputDecodeDivide.lean#L118-L121

import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Emod
import Definitions.Def_Submission_ThreeSum_LightOutputDecodeDivide
set_option autoImplicit false
open ThreeSum ThreeSum.LightOutputDecodeDivide
open Light Light.Emod
set_option maxHeartbeats 1800000
set_option maxRecDepth 7000
variable {lim : Limits} {P : Program} {d : ℕ} {μ ν : ℕ → ℤ} {a Mo V fr : ℕ}

theorem ThreeSum.LightOutputDecodeDivide.time_le_budget {a Mo V : ℕ} (ha : a ≤ V) : time a Mo ≤ budget V := by sorry
