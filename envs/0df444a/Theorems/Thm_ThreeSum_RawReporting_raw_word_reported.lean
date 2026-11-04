-- Prove2me | Theorems.Thm_ThreeSum_RawReporting_raw_word_reported
-- name    : ThreeSum.RawReporting.raw_word_reported
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:14:58.623227+00:00
-- url     : https://prove2.me/theorems/cf6e17af-a26b-428c-a073-d8e52d048768
-- title:
--   Raw Reporting: raw word reported
-- statement:
--   The Raw Reporting construction uses the raw word reported property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/RawReporting.lean#L156-L161
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/RawReporting.lean#L156-L161

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
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

theorem ThreeSum.RawReporting.raw_word_reported {h J : ℕ} (I : Finset (RawItem h J α β γ))
    (r : RawItem h J α β γ) (hr : r ∈ I) :
    word r ∈ frontier I (wantedOf r) J := by sorry
