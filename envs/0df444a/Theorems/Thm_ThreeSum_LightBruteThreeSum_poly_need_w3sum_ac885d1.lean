-- Prove2me | Theorems.Thm_ThreeSum_LightBruteThreeSum_poly_need_w3sum_ac885d1
-- name    : ThreeSum.LightBruteThreeSum.poly_need_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:39:40.86872+00:00
-- url     : https://prove2.me/theorems/d448a5f3-090d-4178-b8f5-e7e2249d2c8b
-- title:
--   Light Brute Three Sum: poly need
-- statement:
--   The Light Brute Three Sum construction uses the poly need property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBruteThreeSum.lean#L65-L82
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBruteThreeSum.lean#L65-L82

import Definitions.Def_Submission_ThreeSum_LightOriginalTripleScan
import Definitions.Def_Submission_ThreeSum_OriginalThreeSum
import Definitions.Def_Submission_ThreeSum_LightBruteThreeSum
set_option autoImplicit false
open ThreeSum ThreeSum.LightBruteThreeSum
open Light ThreeSumApsp.Spec
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightBruteThreeSum.poly_need_w3sum_ac885d1 : PolyNeed need := by sorry
