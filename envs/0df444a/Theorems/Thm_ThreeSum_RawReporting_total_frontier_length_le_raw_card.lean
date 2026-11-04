-- Prove2me | Theorems.Thm_ThreeSum_RawReporting_total_frontier_length_le_raw_card
-- name    : ThreeSum.RawReporting.total_frontier_length_le_raw_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:19:17.978319+00:00
-- url     : https://prove2.me/theorems/23ce5d3e-f4f4-43ee-a0b4-8f9c3ca53092
-- title:
--   Raw Reporting: total frontier length le raw card
-- statement:
--   Summing all wanted-query frontiers still costs at most the original raw
--   mass at a fixed depth: wanted labels form disjoint raw fibers.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/RawReporting.lean#L145-L154
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/RawReporting.lean#L145-L154

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

theorem ThreeSum.RawReporting.total_frontier_length_le_raw_card {h J k : ℕ} (I : Finset (RawItem h J α β γ))
    (hk : k ≤ J) : (∑ w : Wanted h J α, (frontier I w k).length) ≤ I.card := by sorry
