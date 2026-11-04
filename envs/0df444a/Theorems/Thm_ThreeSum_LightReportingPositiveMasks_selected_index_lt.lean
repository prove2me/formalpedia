-- Prove2me | Theorems.Thm_ThreeSum_LightReportingPositiveMasks_selected_index_lt
-- name    : ThreeSum.LightReportingPositiveMasks.selected_index_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:46:34.770205+00:00
-- url     : https://prove2.me/theorems/8dd52476-7632-4132-ab73-a5550b4c114d
-- title:
--   Light Reporting Positive Masks: selected index lt
-- statement:
--   The Light Reporting Positive Masks construction uses the selected index lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightReportingPositiveMasks.lean#L30-L35
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightReportingPositiveMasks.lean#L30-L35

import Definitions.Def_Submission_ThreeSum_LightReportingGatherPair
import Definitions.Def_Submission_ThreeSum_ReportingHostPositive
import Definitions.Def_Submission_ThreeSum_LightReportingPositiveMasks
set_option autoImplicit false
open ThreeSum ThreeSum.LightReportingPositiveMasks
open Light Finset ThreeSum.SubsetAddress
open BlockRows BlockIndexedQuery BlockForced StoredReporting GlobalEncoding LocalCoverBounds RawIncidences RawReporting
open LightBlockChildrenIndexed ReportingHostPositive
set_option maxHeartbeats 600000
set_option linter.unusedSectionVars false
variable {lim : Limits}
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

theorem ThreeSum.LightReportingPositiveMasks.selected_index_lt {h J k : ℕ} (I : Finset (RawItem h J α β γ))
    (w : Wanted h J α) (pre : List (Finset (Fin (512*h)))) (hk : k < J)
    {i : ℕ} (hi : i < (selectedIndices I w pre hk).length) :
    (selectedIndices I w pre hk)[i]?.getD 0 < groupSize h := by sorry
