-- Prove2me | Theorems.Thm_ThreeSum_LightReportingSuffixLower_scanMask_zero
-- name    : ThreeSum.LightReportingSuffixLower.scanMask_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:28:38.432937+00:00
-- url     : https://prove2.me/theorems/f0abea00-db31-48ba-a1d8-e6a29bade16c
-- title:
--   Light Reporting Suffix Lower: scan Mask zero
-- statement:
--   The Light Reporting Suffix Lower construction uses the scan Mask zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightReportingSuffixLower.lean#L21-L22
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightReportingSuffixLower.lean#L21-L22

import Definitions.Def_Submission_ThreeSum_LightReportingSuffixCell
import Definitions.Def_Submission_ThreeSum_LightReportingSuffixLower
set_option autoImplicit false
open ThreeSum ThreeSum.LightReportingSuffixLower
open Light Finset ThreeSum.SubsetAddress ThreeSum.LightSubsetAddress
open ReportingHostSuffix MaskErase
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightReportingSuffixLower.scanMask_zero {V : ℕ} (S : Finset (Fin V)) : scanMask S 0 = 0 := by sorry
