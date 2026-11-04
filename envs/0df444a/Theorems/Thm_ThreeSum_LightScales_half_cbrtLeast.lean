-- Prove2me | Theorems.Thm_ThreeSum_LightScales_half_cbrtLeast
-- name    : ThreeSum.LightScales.half_cbrtLeast
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:18:34.073617+00:00
-- url     : https://prove2.me/theorems/db60bc43-e2d5-4ee2-850c-263854caa010
-- title:
--   Light Scales: half cbrt Least
-- statement:
--   The Light Scales construction uses the half cbrt Least property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightScales.lean#L51-L54
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightScales.lean#L51-L54

import Definitions.Def_Submission_ThreeSum_Scales
import Definitions.Def_Submission_ThreeSum_LightSmallDivide
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Seg
import Definitions.Def_Submission_ThreeSum_LightScales
set_option autoImplicit false
open ThreeSum ThreeSum.LightScales
open Light ThreeSum.Scales
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightScales.half_cbrtLeast (m : ℕ) : (cbrtLeast (m+1)+1)/2 = microHalf m+1 := by sorry
