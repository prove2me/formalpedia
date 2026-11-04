-- Prove2me | Theorems.Thm_ThreeSum_ReportingHostPositiveBatch_parentAt_valid
-- name    : ThreeSum.ReportingHostPositiveBatch.parentAt_valid
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:47:52.850676+00:00
-- url     : https://prove2.me/theorems/f3135431-79b6-4275-82e3-de5fca5714a6
-- title:
--   Reporting Host Positive Batch: parent At valid
-- statement:
--   The Reporting Host Positive Batch construction uses the parent At valid property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostPositiveBatch.lean#L57-L61
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostPositiveBatch.lean#L57-L61

import Definitions.Def_Submission_ThreeSum_ReportingHostPositive
import Definitions.Def_Submission_ThreeSum_ReportingHostPositiveBatch
set_option autoImplicit false
open ThreeSum ThreeSum.ReportingHostPositiveBatch
open Finset BlockForced StoredReporting GlobalEncoding LocalCoverBounds RawIncidences RawReporting
open ReportingHostPositive
set_option linter.unusedSectionVars false
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

theorem ThreeSum.ReportingHostPositiveBatch.parentAt_valid {h J k i : ℕ} (q : GlobalOutput h J)
    (pres : List (List (Finset (Fin (512*h))))) (hp : ∀ pre ∈ pres, ValidPrefix q k pre)
    (hi : i < pres.length) : ValidPrefix q k (parentAt pres i) := by sorry
