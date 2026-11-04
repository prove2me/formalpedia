-- Prove2me | Theorems.Thm_ThreeSum_LightBruteThreeSum_solves
-- name    : ThreeSum.LightBruteThreeSum.solves
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:08:42.704971+00:00
-- url     : https://prove2.me/theorems/651ccc70-fb60-442f-a802-45ea74ffc669
-- title:
--   Light Brute Three Sum: solves
-- statement:
--   The Light Brute Three Sum construction uses the solves property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBruteThreeSum.lean#L84-L97
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBruteThreeSum.lean#L84-L97

import Definitions.Def_Submission_ThreeSum_LightOriginalTripleScan
import Definitions.Def_Submission_ThreeSum_OriginalThreeSum
import Definitions.Def_Submission_ThreeSum_LightBruteThreeSum
set_option autoImplicit false
open ThreeSum ThreeSum.LightBruteThreeSum
open Light ThreeSumApsp.Spec
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightBruteThreeSum.solves : Solves s3Task program 3 (fun n _ => time n) need := by sorry
