-- Prove2me | Theorems.Thm_ThreeSum_ReportingHostPrefixCatalog_leftSource_eq
-- name    : ThreeSum.ReportingHostPrefixCatalog.leftSource_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:39:25.67025+00:00
-- url     : https://prove2.me/theorems/2e3c2319-f72e-4030-9240-368213e8f749
-- title:
--   Reporting Host Prefix Catalog: left Source eq
-- statement:
--   The Reporting Host Prefix Catalog construction uses the left Source eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostPrefixCatalog.lean#L97-L98
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostPrefixCatalog.lean#L97-L98

import Definitions.Def_Submission_ThreeSum_LightReportingSuffixBoxes
import Definitions.Def_Submission_ThreeSum_LocalGraph
import Definitions.Def_Submission_ThreeSum_ReportingHostPrefixCatalog
set_option autoImplicit false
open ThreeSum ThreeSum.ReportingHostPrefixCatalog
open Finset LocalGraph LayerCounts BlockRows BlockIndex BlockIndexedQuery
open BlockEncoding BlockForced GlobalEncoding StoredReporting ReportingHostSuffix
set_option linter.unusedSectionVars false
variable {β γ : Type*} [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ]

theorem ThreeSum.ReportingHostPrefixCatalog.leftSource_eq {h J : ℕ} (P : ℤ) (B : Finset β) (b : β → ℤ) (q : GlobalOutput h J) :
    leftSource P B b q = leftSourceOf (outputOccurrences q) P B b := by sorry
