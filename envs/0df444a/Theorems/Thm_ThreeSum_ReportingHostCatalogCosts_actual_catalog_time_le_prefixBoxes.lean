-- Prove2me | Theorems.Thm_ThreeSum_ReportingHostCatalogCosts_actual_catalog_time_le_prefixBoxes
-- name    : ThreeSum.ReportingHostCatalogCosts.actual_catalog_time_le_prefixBoxes
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:46:44.268206+00:00
-- url     : https://prove2.me/theorems/62c5737e-1fd9-42f4-a053-195b015beac0
-- title:
--   Reporting Host Catalog Costs: actual catalog time le prefix Boxes
-- statement:
--   The Reporting Host Catalog Costs construction uses the actual catalog time le prefix Boxes property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostCatalogCosts.lean#L84-L95
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostCatalogCosts.lean#L84-L95

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

theorem ThreeSum.ReportingHostCatalogCosts.actual_catalog_time_le_prefixBoxes {n k : ℕ}
    (hk : k ≤ Scales.blockCount (Scales.inputBits n)) :
    LightReportingSuffixCatalogSetup.time
      (width (Scales.microHalf (Scales.inputBits n)) (Scales.blockCount (Scales.inputBits n)))
      (suffixStage (Scales.blockCount (Scales.inputBits n))
        (512*Scales.microHalf (Scales.inputBits n)) k)
      (Switch.residualSize n k-Switch.actualSwitch n k)
      (k*(512*Scales.microHalf (Scales.inputBits n)))
      (Fintype.card (Prefix (Scales.microHalf (Scales.inputBits n)) k)) ≤
      100000*(width (Scales.microHalf (Scales.inputBits n)) (Scales.blockCount (Scales.inputBits n))+1)^5*
        CostLedger.prefixBoxes n k := by sorry
