-- Prove2me | Theorems.Thm_ThreeSum_ReportingHostCatalogCosts_catalog_time_le_prefixBoxes
-- name    : ThreeSum.ReportingHostCatalogCosts.catalog_time_le_prefixBoxes
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:46:26.795292+00:00
-- url     : https://prove2.me/theorems/47f3a34a-8554-4ab3-9bb0-02967e2aa268
-- title:
--   Reporting Host Catalog Costs: catalog time le prefix Boxes
-- statement:
--   The Reporting Host Catalog Costs construction uses the catalog time le prefix Boxes property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostCatalogCosts.lean#L65-L82
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostCatalogCosts.lean#L65-L82

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

theorem ThreeSum.ReportingHostCatalogCosts.catalog_time_le_prefixBoxes {n h J k : ℕ}
    (hsize : 2*h = Scales.muZero n) (hblocks : J = Scales.blockCount (Scales.inputBits n))
    (hk : k ≤ J) :
    LightReportingSuffixCatalogSetup.time (width h J) (suffixStage J (512*h) k)
      (Switch.residualSize n k-Switch.actualSwitch n k) (k*(512*h))
      (Fintype.card (Prefix h k)) ≤ 100000*(width h J+1)^5*CostLedger.prefixBoxes n k := by sorry
