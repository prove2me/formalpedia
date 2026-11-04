-- Prove2me | Theorems.Thm_ThreeSum_SharedReportingBankRows_occurrence_lt
-- name    : ThreeSum.SharedReportingBankRows.occurrence_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:39:43.37305+00:00
-- url     : https://prove2.me/theorems/b07ea501-7459-47fb-af9b-963e7a47fa72
-- title:
--   Shared Reporting Bank Rows: occurrence lt
-- statement:
--   The Shared Reporting Bank Rows construction uses the occurrence lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SharedReportingBankRows.lean#L46-L53
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SharedReportingBankRows.lean#L46-L53

import Definitions.Def_Submission_ThreeSum_SharedReportingBankLevels
import Definitions.Def_Submission_ThreeSum_SharedReportingBankSourceBounds
import Definitions.Def_Submission_ThreeSum_SharedReportingBankRows
set_option autoImplicit false
open ThreeSum ThreeSum.SharedReportingBankRows
open Light GlobalEncoding BlockIndexedQuery BlockSourceOccurrenceOrder
open SharedReportingBankData SharedReportingBankLayout SharedReportingBankLevels
open LightReportingPrefixCatalog LightReportingSuffixCatalog ReportingHostLevelData
set_option maxHeartbeats 1800000

theorem ThreeSum.SharedReportingBankRows.occurrence_lt {S nb nc s i j : ℕ}
    (he : rank nb nc s i j < pairs S nb nc) : s < S := by sorry
