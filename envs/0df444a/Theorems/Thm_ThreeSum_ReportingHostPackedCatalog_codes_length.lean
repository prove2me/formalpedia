-- Prove2me | Theorems.Thm_ThreeSum_ReportingHostPackedCatalog_codes_length
-- name    : ThreeSum.ReportingHostPackedCatalog.codes_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:04:38.803536+00:00
-- url     : https://prove2.me/theorems/21a92c10-e744-470a-a1f5-86fd687e7ddc
-- title:
--   Reporting Host Packed Catalog: codes length
-- statement:
--   The Reporting Host Packed Catalog construction uses the codes length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostPackedCatalog.lean#L26-L26
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostPackedCatalog.lean#L26-L26

import Definitions.Def_Submission_ThreeSum_ReportingHostPrefixOrder
import Definitions.Def_Submission_ThreeSum_BinarySearch
import Definitions.Def_Submission_ThreeSum_LightReportingPrefixCatalog
import Definitions.Def_Submission_ThreeSum_ReportingHostPackedCatalog
set_option autoImplicit false
open ThreeSum ThreeSum.ReportingHostPackedCatalog
open ThreeSum.SubsetAddress ReportingHostPrefixCatalog ReportingHostPrefixOrder
set_option maxHeartbeats 600000

theorem ThreeSum.ReportingHostPackedCatalog.codes_length (key : ℕ → ℕ) (n : ℕ) : (codes key n).length=n := by sorry
