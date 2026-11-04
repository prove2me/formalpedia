-- Prove2me | Theorems.Thm_ThreeSum_ReportingHostPrefixCatalog_localLeaf_eq_catalogLeaf
-- name    : ThreeSum.ReportingHostPrefixCatalog.localLeaf_eq_catalogLeaf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:40:00.900187+00:00
-- url     : https://prove2.me/theorems/078fcc7d-664c-43a5-8230-c18227f35652
-- title:
--   Reporting Host Prefix Catalog: local Leaf eq catalog Leaf
-- statement:
--   The Reporting Host Prefix Catalog construction uses the local Leaf eq catalog Leaf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostPrefixCatalog.lean#L117-L124
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostPrefixCatalog.lean#L117-L124

import Definitions.Def_Submission_ThreeSum_LightReportingSuffixBoxes
import Definitions.Def_Submission_ThreeSum_LocalGraph
import Definitions.Def_Submission_ThreeSum_ReportingHostPrefixCatalog
set_option autoImplicit false
open ThreeSum ThreeSum.ReportingHostPrefixCatalog
open Finset LocalGraph LayerCounts BlockRows BlockIndex BlockIndexedQuery
open BlockEncoding BlockForced GlobalEncoding StoredReporting ReportingHostSuffix
set_option linter.unusedSectionVars false
variable {β γ : Type*} [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ]

theorem ThreeSum.ReportingHostPrefixCatalog.localLeaf_eq_catalogLeaf {h J k : ℕ} (hk : k ≤ J)
    (P shift : ℤ) (B : Finset β) (C : Finset γ) (b : β → ℤ) (c : γ → ℤ)
    (q : GlobalOutput h J) (pre : List (Finset (Fin (512*h)))) (hp : ValidPrefix q k pre) :
    LightReportingSuffixBoxes.localLeaf hk P shift B C b c q pre =
      leaf hk (outputOccurrences q) P shift B C b c (ofValidPrefix hk q pre hp) := by sorry
