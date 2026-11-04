-- Prove2me | Theorems.Thm_ThreeSum_ReportingHostPrefixCatalog_leftSource_eq_of_occurrences
-- name    : ThreeSum.ReportingHostPrefixCatalog.leftSource_eq_of_occurrences
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:40:37.054006+00:00
-- url     : https://prove2.me/theorems/f5d11a9c-7965-4343-b467-ff9576adde9b
-- title:
--   Reporting Host Prefix Catalog: left Source eq of occurrences
-- statement:
--   The Reporting Host Prefix Catalog construction uses the left Source eq of occurrences property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostPrefixCatalog.lean#L103-L105
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostPrefixCatalog.lean#L103-L105

import Definitions.Def_Submission_ThreeSum_LightReportingSuffixBoxes
import Definitions.Def_Submission_ThreeSum_LocalGraph
import Definitions.Def_Submission_ThreeSum_ReportingHostPrefixCatalog
set_option autoImplicit false
open ThreeSum ThreeSum.ReportingHostPrefixCatalog
open Finset LocalGraph LayerCounts BlockRows BlockIndex BlockIndexedQuery
open BlockEncoding BlockForced GlobalEncoding StoredReporting ReportingHostSuffix
set_option linter.unusedSectionVars false
variable {β γ : Type*} [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ]

theorem ThreeSum.ReportingHostPrefixCatalog.leftSource_eq_of_occurrences {h J : ℕ} (P : ℤ) (B : Finset β) (b : β → ℤ)
    {q q' : GlobalOutput h J} (ho : outputOccurrences q = outputOccurrences q') :
    leftSource P B b q = leftSource P B b q' := by sorry
