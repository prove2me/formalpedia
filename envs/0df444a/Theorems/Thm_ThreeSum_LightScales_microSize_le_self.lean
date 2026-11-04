-- Prove2me | Theorems.Thm_ThreeSum_LightScales_microSize_le_self
-- name    : ThreeSum.LightScales.microSize_le_self
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:18:38.84501+00:00
-- url     : https://prove2.me/theorems/268659e7-debf-4797-a2bb-a0d81c6bf848
-- title:
--   Light Scales: micro Size le self
-- statement:
--   The Light Scales construction uses the micro Size le self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightScales.lean#L27-L28
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightScales.lean#L27-L28

import Definitions.Def_Submission_ThreeSum_Scales
import Definitions.Def_Submission_ThreeSum_LightSmallDivide
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Seg
import Definitions.Def_Submission_ThreeSum_LightScales
set_option autoImplicit false
open ThreeSum ThreeSum.LightScales
open Light ThreeSum.Scales
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightScales.microSize_le_self (m : ℕ) : microSize m ≤ m := by sorry
