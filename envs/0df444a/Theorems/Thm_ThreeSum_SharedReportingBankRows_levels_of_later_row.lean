-- Prove2me | Theorems.Thm_ThreeSum_SharedReportingBankRows_levels_of_later_row
-- name    : ThreeSum.SharedReportingBankRows.levels_of_later_row
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:47:33.8572+00:00
-- url     : https://prove2.me/theorems/000efdd8-ce5e-40ac-b2d3-e60e8c8b8ff1
-- title:
--   Shared Reporting Bank Rows: levels of later row
-- statement:
--   The Shared Reporting Bank Rows construction uses the levels of later row property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SharedReportingBankRows.lean#L100-L113
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SharedReportingBankRows.lean#L100-L113

import Definitions.Def_Submission_ThreeSum_SharedReportingBankLevels
import Definitions.Def_Submission_ThreeSum_SharedReportingBankSourceBounds
import Definitions.Def_Submission_ThreeSum_SharedReportingBankRows
set_option autoImplicit false
open ThreeSum ThreeSum.SharedReportingBankRows
open Light GlobalEncoding BlockIndexedQuery BlockSourceOccurrenceOrder
open SharedReportingBankData SharedReportingBankLayout SharedReportingBankLevels
open LightReportingPrefixCatalog LightReportingSuffixCatalog ReportingHostLevelData
set_option maxHeartbeats 1800000

theorem ThreeSum.SharedReportingBankRows.levels_of_later_row {μ ν : ℕ → ℤ} {record base h J K nextRecord nextBase : ℕ}
    {f g : Finset (Fin (J*(512*h))) → ℤ}
    (H : Built μ record base h J K f g)
    (heq : KeptBut μ ν nextBase nextRecord (5*K))
    (hrecords : record+5*K ≤ nextRecord) (hnext : nextRecord+5*K ≤ base)
    (hpayload : baseAt base h J K ≤ nextBase) : Built ν record base h J K f g := by sorry
