-- Prove2me | Theorems.Thm_ThreeSum_RawReporting_mem_childList
-- name    : ThreeSum.RawReporting.mem_childList
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:19:22.677024+00:00
-- url     : https://prove2.me/theorems/176d7311-9be4-4136-8645-9e56275eb5c7
-- title:
--   Raw Reporting: mem child List
-- statement:
--   The Raw Reporting construction uses the mem child List property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/RawReporting.lean#L30-L41
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/RawReporting.lean#L30-L41

import Definitions.Def_Submission_ThreeSum_RawIncidences
import Definitions.Def_Submission_ThreeSum_Reporting
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Finset.Sort
import Definitions.Def_Submission_ThreeSum_RawReporting
set_option autoImplicit false
open ThreeSum ThreeSum.RawReporting
set_option maxRecDepth 8000
open Finset
open scoped BigOperators
open GlobalEncoding LocalGraph LocalCoverBounds RawIncidences

theorem ThreeSum.RawReporting.mem_childList {L h : ℕ} {Q S : Finset (Fin L)} :
    S ∈ childList Q h ↔ S ∈ Q.powersetCard h := by sorry
