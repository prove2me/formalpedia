-- Prove2me | Theorems.Thm_ThreeSum_RawReporting_total_frontier_length_le_rawMass
-- name    : ThreeSum.RawReporting.total_frontier_length_le_rawMass
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:16:08.485693+00:00
-- url     : https://prove2.me/theorems/3021c003-038e-4b53-9c0c-ed81ad24c8fa
-- title:
--   Raw Reporting: total frontier length le raw Mass
-- statement:
--   The Raw Reporting construction uses the total frontier length le raw Mass property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/RawReporting.lean#L172-L176
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/RawReporting.lean#L172-L176

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

theorem ThreeSum.RawReporting.total_frontier_length_le_rawMass {h J k : ℕ} (P d : ℤ)
    (T : Finset (Original α β γ)) (a : α → ℤ) (b : β → ℤ) (c : γ → ℤ) (hk : k ≤ J) :
    (∑ w : Wanted h J α, (frontier (rawOn h J P d T a b c) w k).length) ≤
      rawMass h J P d T a b c := by sorry
