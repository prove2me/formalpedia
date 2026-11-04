-- Prove2me | Theorems.Thm_ThreeSum_LightReportingSuffixSetup_coreTime_bound
-- name    : ThreeSum.LightReportingSuffixSetup.coreTime_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:34:07.226463+00:00
-- url     : https://prove2.me/theorems/b0ab944b-728c-4b29-a0b3-5b506198d73d
-- title:
--   Light Reporting Suffix Setup: core Time bound
-- statement:
--   The Light Reporting Suffix Setup construction uses the core Time bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightReportingSuffixSetup.lean#L181-L191
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightReportingSuffixSetup.lean#L181-L191

import Definitions.Def_Submission_ThreeSum_LightReportingSuffixTable
import Definitions.Def_Submission_ThreeSum_LightReportingSuffixSetup
set_option autoImplicit false
open ThreeSum ThreeSum.LightReportingSuffixSetup
open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress
open ReportingHostSuffix
variable {lim : Limits}

theorem ThreeSum.LightReportingSuffixSetup.coreTime_bound {W V cut : ℕ} (hV : V ≤ W) (hcut : cut ≤ V) :
    coreTime W V cut ≤ 19000*(W+1)^4*(downsetCap V cut+1) := by sorry
