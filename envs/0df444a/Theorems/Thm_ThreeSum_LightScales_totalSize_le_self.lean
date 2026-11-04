-- Prove2me | Theorems.Thm_ThreeSum_LightScales_totalSize_le_self
-- name    : ThreeSum.LightScales.totalSize_le_self
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:03:16.648517+00:00
-- url     : https://prove2.me/theorems/186d38c8-3974-40c4-a2f5-940a57ae1a94
-- title:
--   Light Scales: total Size le self
-- statement:
--   The Light Scales construction uses the total Size le self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightScales.lean#L36-L38
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightScales.lean#L36-L38

import Definitions.Def_Submission_ThreeSum_Scales
import Definitions.Def_Submission_ThreeSum_LightSmallDivide
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Seg
import Definitions.Def_Submission_ThreeSum_LightScales
set_option autoImplicit false
open ThreeSum ThreeSum.LightScales
open Light ThreeSum.Scales
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightScales.totalSize_le_self (m : ℕ) : totalSize m ≤ m := by sorry
