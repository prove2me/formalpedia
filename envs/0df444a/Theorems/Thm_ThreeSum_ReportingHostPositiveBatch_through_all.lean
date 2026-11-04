-- Prove2me | Theorems.Thm_ThreeSum_ReportingHostPositiveBatch_through_all
-- name    : ThreeSum.ReportingHostPositiveBatch.through_all
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:46:52.652811+00:00
-- url     : https://prove2.me/theorems/a01c28e4-5695-4260-b0d0-24bc2e6e5149
-- title:
--   Reporting Host Positive Batch: through all
-- statement:
--   The Reporting Host Positive Batch construction uses the through all property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostPositiveBatch.lean#L52-L55
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostPositiveBatch.lean#L52-L55

import Definitions.Def_Submission_ThreeSum_ReportingHostPositive
import Definitions.Def_Submission_ThreeSum_ReportingHostPositiveBatch
set_option autoImplicit false
open ThreeSum ThreeSum.ReportingHostPositiveBatch
open Finset BlockForced StoredReporting GlobalEncoding LocalCoverBounds RawIncidences RawReporting
open ReportingHostPositive
set_option linter.unusedSectionVars false
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

theorem ThreeSum.ReportingHostPositiveBatch.through_all {h J k : ℕ} (I : Finset (RawItem h J α β γ)) (w : Wanted h J α)
    (pres : List (List (Finset (Fin (512*h))))) (hk : k < J) :
    through I w pres hk pres.length = pres.flatMap (fun pre => positiveChildren I w pre hk) := by sorry
