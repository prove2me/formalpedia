-- Prove2me | Theorems.Thm_ThreeSum_ReportingHostPrefixCatalog_leftSet_ofValidPrefix
-- name    : ThreeSum.ReportingHostPrefixCatalog.leftSet_ofValidPrefix
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:41:46.9955+00:00
-- url     : https://prove2.me/theorems/2fb3f07f-8416-4160-abca-6773b998f190
-- title:
--   Reporting Host Prefix Catalog: left Set of Valid Prefix
-- statement:
--   The Reporting Host Prefix Catalog construction uses the left Set of Valid Prefix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostPrefixCatalog.lean#L64-L72
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostPrefixCatalog.lean#L64-L72

import Definitions.Def_Submission_ThreeSum_LightReportingSuffixBoxes
import Definitions.Def_Submission_ThreeSum_LocalGraph
import Definitions.Def_Submission_ThreeSum_ReportingHostPrefixCatalog
set_option autoImplicit false
open ThreeSum ThreeSum.ReportingHostPrefixCatalog
open Finset LocalGraph LayerCounts BlockRows BlockIndex BlockIndexedQuery
open BlockEncoding BlockForced GlobalEncoding StoredReporting ReportingHostSuffix
set_option linter.unusedSectionVars false

theorem ThreeSum.ReportingHostPrefixCatalog.leftSet_ofValidPrefix {h J k : ℕ} (hk : k ≤ J) (q : GlobalOutput h J)
    (pre : List (Finset (Fin (512*h)))) (hp : ValidPrefix q k pre) :
    leftSet (ofValidPrefix hk q pre hp) = leftPrefix k (prefixRows (J := J) pre) := by sorry
