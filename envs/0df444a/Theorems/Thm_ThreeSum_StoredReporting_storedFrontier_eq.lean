-- Prove2me | Theorems.Thm_ThreeSum_StoredReporting_storedFrontier_eq
-- name    : ThreeSum.StoredReporting.storedFrontier_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:32:34.097374+00:00
-- url     : https://prove2.me/theorems/1dd191aa-a8b1-43f0-8ce1-c8c1f41b25f8
-- title:
--   Stored Reporting: stored Frontier eq
-- statement:
--   The Stored Reporting construction uses the stored Frontier eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/StoredReporting.lean#L169-L176
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/StoredReporting.lean#L169-L176

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

theorem ThreeSum.StoredReporting.storedFrontier_eq {h J k : ℕ} (P d : ℤ)
    (A : Finset α) (B : Finset β) (C : Finset γ)
    (a : α → ℤ) (b : β → ℤ) (c : γ → ℤ) (w : Wanted h J α) (hk : k ≤ J) :
    storedFrontier P d A B C a b c w k =
      RawReporting.frontier (rawOn h J P d (A ×ˢ (B ×ˢ C)) a b c) w k := by sorry
