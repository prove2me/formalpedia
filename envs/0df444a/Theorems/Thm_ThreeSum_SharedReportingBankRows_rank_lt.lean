-- Prove2me | Theorems.Thm_ThreeSum_SharedReportingBankRows_rank_lt
-- name    : ThreeSum.SharedReportingBankRows.rank_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:37:52.469854+00:00
-- url     : https://prove2.me/theorems/523829da-b181-4d61-b9dc-cb9ed088e0be
-- title:
--   Shared Reporting Bank Rows: rank lt
-- statement:
--   The Shared Reporting Bank Rows construction uses the rank lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SharedReportingBankRows.lean#L35-L44
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SharedReportingBankRows.lean#L35-L44

import Definitions.Def_Submission_ThreeSum_SharedReportingBankLevels
import Definitions.Def_Submission_ThreeSum_SharedReportingBankSourceBounds
import Definitions.Def_Submission_ThreeSum_SharedReportingBankRows
set_option autoImplicit false
open ThreeSum ThreeSum.SharedReportingBankRows
open Light GlobalEncoding BlockIndexedQuery BlockSourceOccurrenceOrder
open SharedReportingBankData SharedReportingBankLayout SharedReportingBankLevels
open LightReportingPrefixCatalog LightReportingSuffixCatalog ReportingHostLevelData
set_option maxHeartbeats 1800000

theorem ThreeSum.SharedReportingBankRows.rank_lt {S nb nc s i j : ℕ} (hs : s < S) (hi : i < nb) (hj : j < nc) :
    rank nb nc s i j < pairs S nb nc := by sorry
