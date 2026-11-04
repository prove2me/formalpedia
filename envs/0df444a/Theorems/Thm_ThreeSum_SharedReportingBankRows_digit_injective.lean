-- Prove2me | Theorems.Thm_ThreeSum_SharedReportingBankRows_digit_injective
-- name    : ThreeSum.SharedReportingBankRows.digit_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:40:01.376964+00:00
-- url     : https://prove2.me/theorems/2b80e950-38d2-44cd-83ef-58641a781341
-- title:
--   Shared Reporting Bank Rows: digit injective
-- statement:
--   The Shared Reporting Bank Rows construction uses the digit injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SharedReportingBankRows.lean#L21-L26
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SharedReportingBankRows.lean#L21-L26

import Definitions.Def_Submission_ThreeSum_SharedReportingBankLevels
import Definitions.Def_Submission_ThreeSum_SharedReportingBankSourceBounds
import Definitions.Def_Submission_ThreeSum_SharedReportingBankRows
set_option autoImplicit false
open ThreeSum ThreeSum.SharedReportingBankRows
open Light GlobalEncoding BlockIndexedQuery BlockSourceOccurrenceOrder
open SharedReportingBankData SharedReportingBankLayout SharedReportingBankLevels
open LightReportingPrefixCatalog LightReportingSuffixCatalog ReportingHostLevelData
set_option maxHeartbeats 1800000

theorem ThreeSum.SharedReportingBankRows.digit_injective {n a b c d : ℕ} (hb : b < n) (hd : d < n)
    (he : a*n+b=c*n+d) : a=c ∧ b=d := by sorry
