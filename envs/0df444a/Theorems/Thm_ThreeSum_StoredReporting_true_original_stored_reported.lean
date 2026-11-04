-- Prove2me | Theorems.Thm_ThreeSum_StoredReporting_true_original_stored_reported
-- name    : ThreeSum.StoredReporting.true_original_stored_reported
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:01:30.315881+00:00
-- url     : https://prove2.me/theorems/20dd82a6-3cfa-411a-a151-d3b456364374
-- title:
--   Stored Reporting: true original stored reported
-- statement:
--   The Stored Reporting construction uses the true original stored reported property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/StoredReporting.lean#L199-L207
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/StoredReporting.lean#L199-L207

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

theorem ThreeSum.StoredReporting.true_original_stored_reported {h J : ℕ} {P d : ℤ}
    (A : Finset α) (B : Finset β) (C : Finset γ)
    (a : α → ℤ) (b : β → ℤ) (c : γ → ℤ) (hh : 0 < h) (hP : 0 < P)
    (t : Original α β γ) (ht : t ∈ A ×ˢ (B ×ˢ C)) (he : difference a b c t = 0) :
    ∃ r ∈ rawOn h J P d (A ×ˢ (B ×ˢ C)) a b c, r.1 = t ∧
      word r ∈ storedFrontier P d A B C a b c (wantedOf r) J := by sorry
