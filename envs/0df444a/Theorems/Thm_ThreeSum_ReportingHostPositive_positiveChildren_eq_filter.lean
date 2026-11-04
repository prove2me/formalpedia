-- Prove2me | Theorems.Thm_ThreeSum_ReportingHostPositive_positiveChildren_eq_filter
-- name    : ThreeSum.ReportingHostPositive.positiveChildren_eq_filter
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:44:02.790175+00:00
-- url     : https://prove2.me/theorems/742e360c-0c6e-4061-80e5-8429c7d1acb7
-- title:
--   Reporting Host Positive: positive Children eq filter
-- statement:
--   The Reporting Host Positive construction uses the positive Children eq filter property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostPositive.lean#L56-L65
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostPositive.lean#L56-L65

import Definitions.Def_Submission_ThreeSum_LightReportingCatalogExpand
import Definitions.Def_Submission_ThreeSum_ReportingHostFrontier
import Definitions.Def_Submission_ThreeSum_ReportingHostPositive
import Theorems.Thm_Light_Ends_next

set_option autoImplicit false
open ThreeSum ThreeSum.ReportingHostPositive
open Light Finset ThreeSum.SubsetAddress
open BlockForced StoredReporting GlobalEncoding LocalCoverBounds RawIncidences RawReporting
open LightBlockChildrenIndexed ReportingHostFrontier
open scoped BigOperators
set_option linter.unusedSectionVars false
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

theorem ThreeSum.ReportingHostPositive.positiveChildren_eq_filter {h J k : ℕ} (I : Finset (RawItem h J α β γ))
    (w : Wanted h J α) (pre : List (Finset (Fin (512*h)))) (hk : k < J) :
    positiveChildren I w pre hk =
      (childPrefixes w.2.2 pre hk).filter (fun next => 0 < prefixQuery I w (k+1) next) := by sorry
