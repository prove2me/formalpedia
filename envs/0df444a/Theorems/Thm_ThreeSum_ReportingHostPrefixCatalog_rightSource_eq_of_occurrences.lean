-- Prove2me | Theorems.Thm_ThreeSum_ReportingHostPrefixCatalog_rightSource_eq_of_occurrences
-- name    : ThreeSum.ReportingHostPrefixCatalog.rightSource_eq_of_occurrences
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:39:55.430522+00:00
-- url     : https://prove2.me/theorems/967c7a30-006d-4283-9c69-d67d923797a3
-- title:
--   Reporting Host Prefix Catalog: right Source eq of occurrences
-- statement:
--   The Reporting Host Prefix Catalog construction uses the right Source eq of occurrences property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostPrefixCatalog.lean#L107-L109
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostPrefixCatalog.lean#L107-L109

import Definitions.Def_Submission_ThreeSum_LightReportingSuffixBoxes
import Definitions.Def_Submission_ThreeSum_LocalGraph
import Definitions.Def_Submission_ThreeSum_ReportingHostPrefixCatalog
set_option autoImplicit false
open ThreeSum ThreeSum.ReportingHostPrefixCatalog
open Finset LocalGraph LayerCounts BlockRows BlockIndex BlockIndexedQuery
open BlockEncoding BlockForced GlobalEncoding StoredReporting ReportingHostSuffix
set_option linter.unusedSectionVars false
variable {β γ : Type*} [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ]

theorem ThreeSum.ReportingHostPrefixCatalog.rightSource_eq_of_occurrences {h J : ℕ} (P shift : ℤ) (C : Finset γ) (c : γ → ℤ)
    {q q' : GlobalOutput h J} (ho : outputOccurrences q = outputOccurrences q') :
    rightSource P shift C c q = rightSource P shift C c q' := by sorry
