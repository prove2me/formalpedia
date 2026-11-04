-- Prove2me | Theorems.Thm_ThreeSum_ReportingHostCatalogIndexCosts_valueBound_le
-- name    : ThreeSum.ReportingHostCatalogIndexCosts.valueBound_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:15:50.199571+00:00
-- url     : https://prove2.me/theorems/06b13160-02b4-413f-b22e-59f95860b16f
-- title:
--   Reporting Host Catalog Index Costs: value Bound le
-- statement:
--   The Reporting Host Catalog Index Costs construction uses the value Bound le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostCatalogIndexCosts.lean#L18-L27
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostCatalogIndexCosts.lean#L18-L27

import Definitions.Def_Submission_ThreeSum_LightReportingSortedCatalog
import Definitions.Def_Submission_ThreeSum_LightReportingCatalogLookup
import Definitions.Def_Submission_ThreeSum_ReportingHostCatalogIndexCosts
set_option autoImplicit false
open ThreeSum ThreeSum.ReportingHostCatalogIndexCosts
open Light ThreeSum.LightPascal
set_option maxHeartbeats 300000

theorem ThreeSum.ReportingHostCatalogIndexCosts.valueBound_le {W n : ℕ} (hn : n ≤ 2^(2*W)) :
    LightReportingCatalogLookup.valueBound W n ≤ 2^(4*W+1) := by sorry
