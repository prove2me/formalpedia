-- Prove2me | Theorems.Thm_ThreeSum_ReportingHostCatalogIndexCosts_sort_clog_le
-- name    : ThreeSum.ReportingHostCatalogIndexCosts.sort_clog_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:15:57.687346+00:00
-- url     : https://prove2.me/theorems/9b8c6f58-b027-46f7-b9cb-1af26c76e262
-- title:
--   Reporting Host Catalog Index Costs: sort clog le
-- statement:
--   The Reporting Host Catalog Index Costs construction uses the sort clog le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostCatalogIndexCosts.lean#L41-L42
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostCatalogIndexCosts.lean#L41-L42

import Definitions.Def_Submission_ThreeSum_LightReportingSortedCatalog
import Definitions.Def_Submission_ThreeSum_LightReportingCatalogLookup
import Definitions.Def_Submission_ThreeSum_ReportingHostCatalogIndexCosts
set_option autoImplicit false
open ThreeSum ThreeSum.ReportingHostCatalogIndexCosts
open Light ThreeSum.LightPascal
set_option maxHeartbeats 300000

theorem ThreeSum.ReportingHostCatalogIndexCosts.sort_clog_le {W n : ℕ} (hn : n ≤ 2^(2*W)) : Nat.clog 2 n ≤ 2*W := by sorry
