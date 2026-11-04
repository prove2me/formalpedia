-- Prove2me | Theorems.Thm_ThreeSum_LightReportingSuffixLower_scanMask_all
-- name    : ThreeSum.LightReportingSuffixLower.scanMask_all
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:29:02.530211+00:00
-- url     : https://prove2.me/theorems/6b2b5db7-0bb8-4cf4-a920-d8c48750a7df
-- title:
--   Light Reporting Suffix Lower: scan Mask all
-- statement:
--   The Light Reporting Suffix Lower construction uses the scan Mask all property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightReportingSuffixLower.lean#L24-L26
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightReportingSuffixLower.lean#L24-L26

import Definitions.Def_Submission_ThreeSum_LightReportingSuffixCell
import Definitions.Def_Submission_ThreeSum_LightReportingSuffixLower
set_option autoImplicit false
open ThreeSum ThreeSum.LightReportingSuffixLower
open Light Finset ThreeSum.SubsetAddress ThreeSum.LightSubsetAddress
open ReportingHostSuffix MaskErase
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightReportingSuffixLower.scanMask_all {V : ℕ} (S : Finset (Fin V)) : scanMask S V = subsetMask S := by sorry
