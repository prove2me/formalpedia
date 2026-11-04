-- Prove2me | Theorems.Thm_ThreeSum_ReportingHostPositiveBatch_flatMap_length_le
-- name    : ThreeSum.ReportingHostPositiveBatch.flatMap_length_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:46:44.660104+00:00
-- url     : https://prove2.me/theorems/9b74dc94-c807-43a2-b801-911368b30b85
-- title:
--   Reporting Host Positive Batch: flat Map length le
-- statement:
--   The Reporting Host Positive Batch construction uses the flat Map length le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostPositiveBatch.lean#L12-L20
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostPositiveBatch.lean#L12-L20

import Definitions.Def_Submission_ThreeSum_ReportingHostPositive
import Definitions.Def_Submission_ThreeSum_ReportingHostPositiveBatch
set_option autoImplicit false
open ThreeSum ThreeSum.ReportingHostPositiveBatch
open Finset BlockForced StoredReporting GlobalEncoding LocalCoverBounds RawIncidences RawReporting
open ReportingHostPositive
set_option linter.unusedSectionVars false

theorem ThreeSum.ReportingHostPositiveBatch.flatMap_length_le {α β : Type*} (xs : List α) (f : α → List β) (G : ℕ)
    (hf : ∀ x ∈ xs, (f x).length ≤ G) : (xs.flatMap f).length ≤ xs.length*G := by sorry
