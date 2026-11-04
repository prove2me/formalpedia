-- Prove2me | Theorems.Thm_ThreeSum_ReportingHostPrefixCatalog_rightSet_ofValidPrefix
-- name    : ThreeSum.ReportingHostPrefixCatalog.rightSet_ofValidPrefix
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:39:54.776701+00:00
-- url     : https://prove2.me/theorems/37691796-e84f-42af-9980-61fd786b392b
-- title:
--   Reporting Host Prefix Catalog: right Set of Valid Prefix
-- statement:
--   The Reporting Host Prefix Catalog construction uses the right Set of Valid Prefix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostPrefixCatalog.lean#L74-L83
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostPrefixCatalog.lean#L74-L83

import Definitions.Def_Submission_ThreeSum_LightReportingSuffixBoxes
import Definitions.Def_Submission_ThreeSum_LocalGraph
import Definitions.Def_Submission_ThreeSum_ReportingHostPrefixCatalog
set_option autoImplicit false
open ThreeSum ThreeSum.ReportingHostPrefixCatalog
open Finset LocalGraph LayerCounts BlockRows BlockIndex BlockIndexedQuery
open BlockEncoding BlockForced GlobalEncoding StoredReporting ReportingHostSuffix
set_option linter.unusedSectionVars false

theorem ThreeSum.ReportingHostPrefixCatalog.rightSet_ofValidPrefix {h J k : ℕ} (hk : k ≤ J) (q : GlobalOutput h J)
    (pre : List (Finset (Fin (512*h)))) (hp : ValidPrefix q k pre) :
    rightSet (ofValidPrefix hk q pre hp) =
      rightPrefix k (outputRows q) (prefixRows (J := J) pre) := by sorry
