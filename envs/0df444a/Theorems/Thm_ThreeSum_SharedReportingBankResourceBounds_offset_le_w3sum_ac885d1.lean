-- Prove2me | Theorems.Thm_ThreeSum_SharedReportingBankResourceBounds_offset_le_w3sum_ac885d1
-- name    : ThreeSum.SharedReportingBankResourceBounds.offset_le_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T14:19:39.442436+00:00
-- url     : https://prove2.me/theorems/3fb50232-953b-4cd8-84c5-ca9cf762334c
-- title:
--   Shared Reporting Bank Resource Bounds: offset le
-- statement:
--   The Shared Reporting Bank Resource Bounds construction uses the offset le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SharedReportingBankResourceBounds.lean#L92-L103
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SharedReportingBankResourceBounds.lean#L92-L103

import Definitions.Def_Submission_ThreeSum_SharedReportingBankCosts
import Definitions.Def_Submission_ThreeSum_PolynomialResources
import Definitions.Def_Submission_ThreeSum_SharedReportingBankResourceBounds
import Theorems.Thm_ThreeSum_SourceBuckets_offset_le

set_option autoImplicit false
open ThreeSum ThreeSum.SharedReportingBankResourceBounds
open Light SubsetAddress SharedReportingBankLayout SharedReportingBankLevels
open SharedReportingBankHeader SharedReportingBankRows
set_option maxHeartbeats 2800000
set_option maxRecDepth 14000

theorem ThreeSum.SharedReportingBankResourceBounds.offset_le_w3sum_ac885d1 (h J : ℕ) : offset h J (levels J) ≤ levels J*cellBound h J := by sorry
