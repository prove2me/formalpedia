-- Prove2me | Theorems.Thm_ThreeSum_ReportingHostCatalogCosts_block_catalog_time_le_layer
-- name    : ThreeSum.ReportingHostCatalogCosts.block_catalog_time_le_layer
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:46:25.579166+00:00
-- url     : https://prove2.me/theorems/ff65ea1c-b65c-4a5f-b61c-ff5c8c571402
-- title:
--   Reporting Host Catalog Costs: block catalog time le layer
-- statement:
--   The Reporting Host Catalog Costs construction uses the block catalog time le layer property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostCatalogCosts.lean#L42-L56
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostCatalogCosts.lean#L42-L56

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

theorem ThreeSum.ReportingHostCatalogCosts.block_catalog_time_le_layer {h J k cut : ℕ} (hk : k ≤ J)
    (hcut : cut ≤ residualSize h J k) :
    LightReportingSuffixCatalogSetup.time (width h J) (suffixStage J (512*h) k) cut (k*(512*h))
      (Fintype.card (Prefix h k)) ≤
      100000*(width h J+1)^5*(((512*h).choose (2*h)*(2*h).choose h)^k)*
        (256*residualSize h J k).choose cut := by sorry
