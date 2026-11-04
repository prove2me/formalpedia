-- Prove2me | Theorems.Thm_ThreeSum_ReportingHostPackedCatalog_pairKey_lt
-- name    : ThreeSum.ReportingHostPackedCatalog.pairKey_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:06:46.29903+00:00
-- url     : https://prove2.me/theorems/6a3e87a3-1c2d-4b00-ba7e-274413b78c5b
-- title:
--   Reporting Host Packed Catalog: pair Key lt
-- statement:
--   The Reporting Host Packed Catalog construction uses the pair Key lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostPackedCatalog.lean#L28-L29
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostPackedCatalog.lean#L28-L29

import Definitions.Def_Submission_ThreeSum_ReportingHostPrefixOrder
import Definitions.Def_Submission_ThreeSum_BinarySearch
import Definitions.Def_Submission_ThreeSum_LightReportingPrefixCatalog
import Definitions.Def_Submission_ThreeSum_ReportingHostPackedCatalog
set_option autoImplicit false
open ThreeSum ThreeSum.ReportingHostPackedCatalog
open ThreeSum.SubsetAddress ReportingHostPrefixCatalog ReportingHostPrefixOrder
set_option maxHeartbeats 600000

theorem ThreeSum.ReportingHostPackedCatalog.pairKey_lt {radix left right : ℕ} (hl : left < radix) (hr : right < radix) :
    pairKey radix left right < radix^2 := by sorry
