-- Prove2me | Theorems.Thm_ThreeSum_LightReportingPositiveMasks_ofFn_getD_map
-- name    : ThreeSum.LightReportingPositiveMasks.ofFn_getD_map
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:46:16.968202+00:00
-- url     : https://prove2.me/theorems/1a8ba12a-1b7e-49ed-9f69-dc321fcaee68
-- title:
--   Light Reporting Positive Masks: of Fn get D map
-- statement:
--   The Light Reporting Positive Masks construction uses the of Fn get D map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightReportingPositiveMasks.lean#L15-L20
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightReportingPositiveMasks.lean#L15-L20

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

theorem ThreeSum.LightReportingPositiveMasks.ofFn_getD_map {α β : Type*} (xs : List α) (fallback : α) (f : α → β) :
    List.ofFn (fun i : Fin xs.length => f (xs[i.val]?.getD fallback)) = xs.map f := by sorry
