-- Prove2me | Theorems.Thm_ThreeSum_StoredReporting_storedFrontier_mem_iff
-- name    : ThreeSum.StoredReporting.storedFrontier_mem_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:01:32.950128+00:00
-- url     : https://prove2.me/theorems/0285c921-22ae-4279-ae33-7a4e5a01818d
-- title:
--   Stored Reporting: stored Frontier mem iff
-- statement:
--   The Stored Reporting construction uses the stored Frontier mem iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/StoredReporting.lean#L178-L186
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/StoredReporting.lean#L178-L186

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

theorem ThreeSum.StoredReporting.storedFrontier_mem_iff {h J k : ℕ} (P d : ℤ)
    (A : Finset α) (B : Finset β) (C : Finset γ)
    (a : α → ℤ) (b : β → ℤ) (c : γ → ℤ) (w : Wanted h J α)
    (pre : List (Finset (Fin (512 * h)))) (hk : k ≤ J) :
    pre ∈ storedFrontier P d A B C a b c w k ↔
      ∃ r ∈ rawOn h J P d (A ×ˢ (B ×ˢ C)) a b c,
        wantedOf r = w ∧ (word r).take k = pre := by sorry
