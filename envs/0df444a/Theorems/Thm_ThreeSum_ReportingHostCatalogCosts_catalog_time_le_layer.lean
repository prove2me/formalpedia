-- Prove2me | Theorems.Thm_ThreeSum_ReportingHostCatalogCosts_catalog_time_le_layer
-- name    : ThreeSum.ReportingHostCatalogCosts.catalog_time_le_layer
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:46:28.478747+00:00
-- url     : https://prove2.me/theorems/da0d7a4e-d280-466f-b715-4abd2b7b19c4
-- title:
--   Reporting Host Catalog Costs: catalog time le layer
-- statement:
--   The Reporting Host Catalog Costs construction uses the catalog time le layer property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostCatalogCosts.lean#L25-L40
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostCatalogCosts.lean#L25-L40

import Definitions.Def_Submission_ThreeSum_LightReportingSuffixCatalogSetup
import Definitions.Def_Submission_ThreeSum_ReportingHostPrefixCatalog
import Definitions.Def_Submission_ThreeSum_ReportingHostSuffixCosts
import Definitions.Def_Submission_ThreeSum_CostLedger
import Definitions.Def_Submission_ThreeSum_ReportingHostCatalogCosts
set_option autoImplicit false
open ThreeSum ThreeSum.ReportingHostCatalogCosts
set_option maxRecDepth 8000
open ThreeSum.SubsetAddress ThreeSum.LightBlockQuery ThreeSum.BlockIndexedQuery
open ReportingHostPrefixCatalog ReportingHostSuffixCosts

theorem ThreeSum.ReportingHostCatalogCosts.catalog_time_le_layer {W V offset cut n : ℕ} (hfit : offset+V ≤ W)
    (hhalf : cut ≤ V/2) (hn : 0 < n) :
    LightReportingSuffixCatalogSetup.time W V cut offset n ≤
      100000*(W+1)^5*n*V.choose cut := by sorry
