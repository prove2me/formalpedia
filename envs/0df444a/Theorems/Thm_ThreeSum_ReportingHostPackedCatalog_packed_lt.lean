-- Prove2me | Theorems.Thm_ThreeSum_ReportingHostPackedCatalog_packed_lt
-- name    : ThreeSum.ReportingHostPackedCatalog.packed_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:04:58.476921+00:00
-- url     : https://prove2.me/theorems/4055f804-bb5f-40ef-8348-89f91ca8d889
-- title:
--   Reporting Host Packed Catalog: packed lt
-- statement:
--   The Reporting Host Packed Catalog construction uses the packed lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostPackedCatalog.lean#L40-L41
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostPackedCatalog.lean#L40-L41

import Definitions.Def_Submission_ThreeSum_ReportingHostPrefixOrder
import Definitions.Def_Submission_ThreeSum_BinarySearch
import Definitions.Def_Submission_ThreeSum_LightReportingPrefixCatalog
import Definitions.Def_Submission_ThreeSum_ReportingHostPackedCatalog
set_option autoImplicit false
open ThreeSum ThreeSum.ReportingHostPackedCatalog
open ThreeSum.SubsetAddress ReportingHostPrefixCatalog ReportingHostPrefixOrder
set_option maxHeartbeats 600000

theorem ThreeSum.ReportingHostPackedCatalog.packed_lt {key : ℕ → ℕ} {n i U : ℕ} (hi : i < n) (hk : key i < U) :
    packed key n i < U*(n+1) := by sorry
