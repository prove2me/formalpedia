-- Prove2me | Theorems.Thm_ThreeSum_LightReportingSuffixLower_scanMask_succ
-- name    : ThreeSum.LightReportingSuffixLower.scanMask_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:29:03.079204+00:00
-- url     : https://prove2.me/theorems/3d54cb4a-fbc7-4fd0-a202-c7e615672707
-- title:
--   Light Reporting Suffix Lower: scan Mask succ
-- statement:
--   The Light Reporting Suffix Lower construction uses the scan Mask succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightReportingSuffixLower.lean#L28-L48
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightReportingSuffixLower.lean#L28-L48

import Definitions.Def_Submission_ThreeSum_LightReportingSuffixCell
import Definitions.Def_Submission_ThreeSum_LightReportingSuffixLower
set_option autoImplicit false
open ThreeSum ThreeSum.LightReportingSuffixLower
open Light Finset ThreeSum.SubsetAddress ThreeSum.LightSubsetAddress
open ReportingHostSuffix MaskErase
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightReportingSuffixLower.scanMask_succ {V j : ℕ} (S : Finset (Fin V)) (hj : j < V) :
    scanMask S (j+1) = scanMask S j+if (⟨j,hj⟩ : Fin V) ∈ S then 2^j else 0 := by sorry
