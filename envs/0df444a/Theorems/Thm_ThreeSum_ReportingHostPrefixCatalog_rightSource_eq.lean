-- Prove2me | Theorems.Thm_ThreeSum_ReportingHostPrefixCatalog_rightSource_eq
-- name    : ThreeSum.ReportingHostPrefixCatalog.rightSource_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:39:52.521801+00:00
-- url     : https://prove2.me/theorems/bad3cf1b-70a5-4acd-b91d-4c0f0e997d30
-- title:
--   Reporting Host Prefix Catalog: right Source eq
-- statement:
--   The Reporting Host Prefix Catalog construction uses the right Source eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostPrefixCatalog.lean#L100-L101
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostPrefixCatalog.lean#L100-L101

import Definitions.Def_Submission_ThreeSum_LightReportingSuffixBoxes
import Definitions.Def_Submission_ThreeSum_LocalGraph
import Definitions.Def_Submission_ThreeSum_ReportingHostPrefixCatalog
set_option autoImplicit false
open ThreeSum ThreeSum.ReportingHostPrefixCatalog
open Finset LocalGraph LayerCounts BlockRows BlockIndex BlockIndexedQuery
open BlockEncoding BlockForced GlobalEncoding StoredReporting ReportingHostSuffix
set_option linter.unusedSectionVars false
variable {β γ : Type*} [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ]

theorem ThreeSum.ReportingHostPrefixCatalog.rightSource_eq {h J : ℕ} (P shift : ℤ) (C : Finset γ) (c : γ → ℤ) (q : GlobalOutput h J) :
    rightSource P shift C c q = rightSourceOf (outputOccurrences q) P shift C c := by sorry
