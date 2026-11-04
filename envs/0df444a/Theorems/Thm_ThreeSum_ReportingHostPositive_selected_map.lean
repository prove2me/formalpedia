-- Prove2me | Theorems.Thm_ThreeSum_ReportingHostPositive_selected_map
-- name    : ThreeSum.ReportingHostPositive.selected_map
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:42:57.162774+00:00
-- url     : https://prove2.me/theorems/26d9471e-4514-47ca-8116-e7a98d8499ac
-- title:
--   Reporting Host Positive: selected map
-- statement:
--   The Reporting Host Positive construction uses the selected map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostPositive.lean#L26-L32
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostPositive.lean#L26-L32

import Definitions.Def_Submission_ThreeSum_LightReportingCatalogExpand
import Definitions.Def_Submission_ThreeSum_ReportingHostFrontier
import Definitions.Def_Submission_ThreeSum_ReportingHostPositive
set_option autoImplicit false
open ThreeSum ThreeSum.ReportingHostPositive
open Light Finset ThreeSum.SubsetAddress
open BlockForced StoredReporting GlobalEncoding LocalCoverBounds RawIncidences RawReporting
open LightBlockChildrenIndexed ReportingHostFrontier
open scoped BigOperators
set_option linter.unusedSectionVars false

theorem ThreeSum.ReportingHostPositive.selected_map {α : Type*} (xs : List α) (fallback : α) (q : α → ℕ) :
    (LightReportingFilter.selected (fun i => q (xs[i]?.getD fallback)) xs.length).map
        (fun i => xs[i]?.getD fallback) = xs.filter (fun x => 0 < q x) := by sorry
