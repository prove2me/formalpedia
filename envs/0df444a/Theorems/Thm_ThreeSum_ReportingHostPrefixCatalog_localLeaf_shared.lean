-- Prove2me | Theorems.Thm_ThreeSum_ReportingHostPrefixCatalog_localLeaf_shared
-- name    : ThreeSum.ReportingHostPrefixCatalog.localLeaf_shared
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:41:06.447286+00:00
-- url     : https://prove2.me/theorems/a22ae63c-5746-477a-9963-8ddaeb359713
-- title:
--   Reporting Host Prefix Catalog: local Leaf shared
-- statement:
--   The Reporting Host Prefix Catalog construction uses the local Leaf shared property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostPrefixCatalog.lean#L126-L135
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostPrefixCatalog.lean#L126-L135

import Definitions.Def_Submission_ThreeSum_LightReportingSuffixBoxes
import Definitions.Def_Submission_ThreeSum_LocalGraph
import Definitions.Def_Submission_ThreeSum_ReportingHostPrefixCatalog
set_option autoImplicit false
open ThreeSum ThreeSum.ReportingHostPrefixCatalog
open Finset LocalGraph LayerCounts BlockRows BlockIndex BlockIndexedQuery
open BlockEncoding BlockForced GlobalEncoding StoredReporting ReportingHostSuffix
set_option linter.unusedSectionVars false
variable {β γ : Type*} [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ]

theorem ThreeSum.ReportingHostPrefixCatalog.localLeaf_shared {h J k : ℕ} (hk : k ≤ J)
    (P shift : ℤ) (B : Finset β) (C : Finset γ) (b : β → ℤ) (c : γ → ℤ)
    {q q' : GlobalOutput h J} {pre pre' : List (Finset (Fin (512*h)))}
    (hp : ValidPrefix q k pre) (hp' : ValidPrefix q' k pre')
    (ho : outputOccurrences q = outputOccurrences q')
    (hkey : ofValidPrefix hk q pre hp = ofValidPrefix hk q' pre' hp') :
    LightReportingSuffixBoxes.localLeaf hk P shift B C b c q pre =
      LightReportingSuffixBoxes.localLeaf hk P shift B C b c q' pre' := by sorry
