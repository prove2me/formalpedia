-- Prove2me | Theorems.Thm_ThreeSum_ReportingHostCatalogIndexCosts_prefix_lookup_time_le
-- name    : ThreeSum.ReportingHostCatalogIndexCosts.prefix_lookup_time_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:16:23.232886+00:00
-- url     : https://prove2.me/theorems/93e93517-38a6-4456-816b-a4a210a0b148
-- title:
--   Reporting Host Catalog Index Costs: prefix lookup time le
-- statement:
--   The Reporting Host Catalog Index Costs construction uses the prefix lookup time le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostCatalogIndexCosts.lean#L57-L60
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostCatalogIndexCosts.lean#L57-L60

import Definitions.Def_Submission_ThreeSum_LightReportingSortedCatalog
import Definitions.Def_Submission_ThreeSum_LightReportingCatalogLookup
import Definitions.Def_Submission_ThreeSum_ReportingHostCatalogIndexCosts
set_option autoImplicit false
open ThreeSum ThreeSum.ReportingHostCatalogIndexCosts
open Light ThreeSum.LightPascal
set_option maxHeartbeats 300000

theorem ThreeSum.ReportingHostCatalogIndexCosts.prefix_lookup_time_le {h J k : ℕ} (hk : k ≤ J) :
    LightReportingCatalogLookup.time (J*(512*h)) (LightReportingPrefixCatalog.count h k) ≤
      1000*(J*(512*h)+1) := by sorry
