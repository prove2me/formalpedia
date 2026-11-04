-- Prove2me | Theorems.Thm_ThreeSum_LightScales_cbrtLeast_successor
-- name    : ThreeSum.LightScales.cbrtLeast_successor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:18:27.174273+00:00
-- url     : https://prove2.me/theorems/23bd40f7-49a8-43a7-ab90-a5eac79e5178
-- title:
--   Light Scales: cbrt Least successor
-- statement:
--   The Light Scales construction uses the cbrt Least successor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightScales.lean#L40-L49
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightScales.lean#L40-L49

import Definitions.Def_Submission_ThreeSum_Scales
import Definitions.Def_Submission_ThreeSum_LightSmallDivide
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Seg
import Definitions.Def_Submission_ThreeSum_LightScales
set_option autoImplicit false
open ThreeSum ThreeSum.LightScales
open Light ThreeSum.Scales
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightScales.cbrtLeast_successor (m : ℕ) : cbrtLeast (m+1) = Nat.nthRoot 3 m+1 := by sorry
