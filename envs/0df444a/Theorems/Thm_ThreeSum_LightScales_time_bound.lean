-- Prove2me | Theorems.Thm_ThreeSum_LightScales_time_bound
-- name    : ThreeSum.LightScales.time_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:58:47.477044+00:00
-- url     : https://prove2.me/theorems/dc3fc65a-e121-4bac-ba24-79b1cacbacff
-- title:
--   Light Scales: time bound
-- statement:
--   The Light Scales construction uses the time bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightScales.lean#L168-L174
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightScales.lean#L168-L174

import Definitions.Def_Submission_ThreeSum_Scales
import Definitions.Def_Submission_ThreeSum_LightSmallDivide
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Seg
import Definitions.Def_Submission_ThreeSum_LightScales
import Theorems.Thm_ThreeSum_LightSmallDivide_time_bound

set_option autoImplicit false
open ThreeSum ThreeSum.LightScales
open Light ThreeSum.Scales
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightScales.time_bound (n : ℕ) : time n ≤ 500*(inputBits n+1) := by sorry
