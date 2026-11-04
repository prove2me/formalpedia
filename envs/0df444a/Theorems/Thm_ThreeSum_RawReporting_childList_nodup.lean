-- Prove2me | Theorems.Thm_ThreeSum_RawReporting_childList_nodup
-- name    : ThreeSum.RawReporting.childList_nodup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:14:54.654771+00:00
-- url     : https://prove2.me/theorems/c15e04f6-e324-40a4-9117-74710a61e6b4
-- title:
--   Raw Reporting: child List nodup
-- statement:
--   The Raw Reporting construction uses the child List nodup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/RawReporting.lean#L43-L45
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/RawReporting.lean#L43-L45

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

theorem ThreeSum.RawReporting.childList_nodup {L : ℕ} (Q : Finset (Fin L)) (h : ℕ) :
    (childList Q h).Nodup := by sorry
