-- Prove2me | Theorems.Thm_ThreeSum_ReportingHostCatalogIndexCosts_lookup_time_le
-- name    : ThreeSum.ReportingHostCatalogIndexCosts.lookup_time_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:15:38.78171+00:00
-- url     : https://prove2.me/theorems/a91510d3-5839-4f85-a23d-61701a859f4a
-- title:
--   Reporting Host Catalog Index Costs: lookup time le
-- statement:
--   The Reporting Host Catalog Index Costs construction uses the lookup time le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostCatalogIndexCosts.lean#L44-L48
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostCatalogIndexCosts.lean#L44-L48

import Definitions.Def_Submission_ThreeSum_LightReportingSortedCatalog
import Definitions.Def_Submission_ThreeSum_LightReportingCatalogLookup
import Definitions.Def_Submission_ThreeSum_ReportingHostCatalogIndexCosts
set_option autoImplicit false
open ThreeSum ThreeSum.ReportingHostCatalogIndexCosts
open Light ThreeSum.LightPascal
set_option maxHeartbeats 300000

theorem ThreeSum.ReportingHostCatalogIndexCosts.lookup_time_le {W n : ℕ} (hn : n ≤ 2^(2*W)) :
    LightReportingCatalogLookup.time W n ≤ 1000*(W+1) := by sorry
