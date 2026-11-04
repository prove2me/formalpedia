-- Prove2me | Theorems.Thm_ThreeSum_ReportingHostPositiveBatch_parentAt_eq_get
-- name    : ThreeSum.ReportingHostPositiveBatch.parentAt_eq_get
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:48:05.5788+00:00
-- url     : https://prove2.me/theorems/75c0acee-446e-4212-b670-2ce002f1beaa
-- title:
--   Reporting Host Positive Batch: parent At eq get
-- statement:
--   The Reporting Host Positive Batch construction uses the parent At eq get property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostPositiveBatch.lean#L27-L28
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostPositiveBatch.lean#L27-L28

import Definitions.Def_Submission_ThreeSum_ReportingHostPositive
import Definitions.Def_Submission_ThreeSum_ReportingHostPositiveBatch
set_option autoImplicit false
open ThreeSum ThreeSum.ReportingHostPositiveBatch
open Finset BlockForced StoredReporting GlobalEncoding LocalCoverBounds RawIncidences RawReporting
open ReportingHostPositive
set_option linter.unusedSectionVars false
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

theorem ThreeSum.ReportingHostPositiveBatch.parentAt_eq_get {h i : ℕ} (pres : List (List (Finset (Fin (512*h))))) (hi : i < pres.length) :
    parentAt pres i = pres[i] := by sorry
