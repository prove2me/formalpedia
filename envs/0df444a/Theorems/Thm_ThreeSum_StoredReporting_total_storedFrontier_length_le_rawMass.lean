-- Prove2me | Theorems.Thm_ThreeSum_StoredReporting_total_storedFrontier_length_le_rawMass
-- name    : ThreeSum.StoredReporting.total_storedFrontier_length_le_rawMass
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:01:33.981638+00:00
-- url     : https://prove2.me/theorems/2df95556-d3bf-40a3-ae74-a6892ae75dee
-- title:
--   Stored Reporting: total stored Frontier length le raw Mass
-- statement:
--   The actual query formula discharges the reporting interface. Summed
--   positive frontiers, over every A/lift/occurrence/Q wanted key, cost at most
--   the original raw mass at each depth.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/StoredReporting.lean#L191-L197
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/StoredReporting.lean#L191-L197

import Definitions.Def_Submission_ThreeSum_BlockForced
import Definitions.Def_Submission_ThreeSum_StoredReporting
set_option autoImplicit false
open ThreeSum ThreeSum.StoredReporting
set_option maxRecDepth 8000
open Finset
open scoped BigOperators
open GlobalEncoding LocalGraph LocalCoverBounds RawIncidences RawReporting RawPrefixCounts
open BlockRows BlockEncoding BlockForced
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

theorem ThreeSum.StoredReporting.total_storedFrontier_length_le_rawMass {h J k : ℕ} (P d : ℤ)
    (A : Finset α) (B : Finset β) (C : Finset γ)
    (a : α → ℤ) (b : β → ℤ) (c : γ → ℤ) (hk : k ≤ J) :
    (∑ w : Wanted h J α, (storedFrontier P d A B C a b c w k).length) ≤
      rawMass h J P d (A ×ˢ (B ×ˢ C)) a b c := by sorry
