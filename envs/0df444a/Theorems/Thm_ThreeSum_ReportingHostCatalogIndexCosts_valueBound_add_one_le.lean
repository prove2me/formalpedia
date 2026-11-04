-- Prove2me | Theorems.Thm_ThreeSum_ReportingHostCatalogIndexCosts_valueBound_add_one_le
-- name    : ThreeSum.ReportingHostCatalogIndexCosts.valueBound_add_one_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:16:00.665331+00:00
-- url     : https://prove2.me/theorems/b508065f-3667-4ebf-bbc4-0fef932c4a2e
-- title:
--   Reporting Host Catalog Index Costs: value Bound add one le
-- statement:
--   The Reporting Host Catalog Index Costs construction uses the value Bound add one le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostCatalogIndexCosts.lean#L29-L35
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostCatalogIndexCosts.lean#L29-L35

import Definitions.Def_Submission_ThreeSum_LightReportingSortedCatalog
import Definitions.Def_Submission_ThreeSum_LightReportingCatalogLookup
import Definitions.Def_Submission_ThreeSum_ReportingHostCatalogIndexCosts
set_option autoImplicit false
open ThreeSum ThreeSum.ReportingHostCatalogIndexCosts
open Light ThreeSum.LightPascal
set_option maxHeartbeats 300000

theorem ThreeSum.ReportingHostCatalogIndexCosts.valueBound_add_one_le {W n : ℕ} (hn : n ≤ 2^(2*W)) :
    LightReportingCatalogLookup.valueBound W n+1 ≤ 2^(4*W+2) := by sorry
