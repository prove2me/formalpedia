-- Prove2me | Theorems.Thm_ThreeSum_ReportingHostCatalogIndexCosts_remainder_log_le
-- name    : ThreeSum.ReportingHostCatalogIndexCosts.remainder_log_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:16:00.156349+00:00
-- url     : https://prove2.me/theorems/9452dd52-8cf8-48e0-a602-6402e56daea3
-- title:
--   Reporting Host Catalog Index Costs: remainder log le
-- statement:
--   The Reporting Host Catalog Index Costs construction uses the remainder log le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostCatalogIndexCosts.lean#L37-L39
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostCatalogIndexCosts.lean#L37-L39

import Definitions.Def_Submission_ThreeSum_LightReportingSortedCatalog
import Definitions.Def_Submission_ThreeSum_LightReportingCatalogLookup
import Definitions.Def_Submission_ThreeSum_ReportingHostCatalogIndexCosts
set_option autoImplicit false
open ThreeSum ThreeSum.ReportingHostCatalogIndexCosts
open Light ThreeSum.LightPascal
set_option maxHeartbeats 300000

theorem ThreeSum.ReportingHostCatalogIndexCosts.remainder_log_le {W n : ℕ} (hn : n ≤ 2^(2*W)) :
    Nat.log 2 (LightReportingCatalogLookup.valueBound W n+1) ≤ 4*W+2 := by sorry
