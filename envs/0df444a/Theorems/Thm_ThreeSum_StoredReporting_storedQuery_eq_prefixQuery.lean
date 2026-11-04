-- Prove2me | Theorems.Thm_ThreeSum_StoredReporting_storedQuery_eq_prefixQuery
-- name    : ThreeSum.StoredReporting.storedQuery_eq_prefixQuery
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:12:53.566809+00:00
-- url     : https://prove2.me/theorems/7f04cc44-9f0c-4d86-88c4-70d5325a4b39
-- title:
--   Stored Reporting: stored Query eq prefix Query
-- statement:
--   The Stored Reporting construction uses the stored Query eq prefix Query property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/StoredReporting.lean#L142-L149
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/StoredReporting.lean#L142-L149

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

theorem ThreeSum.StoredReporting.storedQuery_eq_prefixQuery {h J k : ℕ} (P d : ℤ)
    (A : Finset α) (B : Finset β) (C : Finset γ)
    (a : α → ℤ) (b : β → ℤ) (c : γ → ℤ) (w : Wanted h J α)
    (pre : List (Finset (Fin (512 * h)))) (hk : k ≤ J) :
    storedQuery P d A B C a b c w k pre =
      prefixQuery (rawOn h J P d (A ×ˢ (B ×ˢ C)) a b c) w k pre := by sorry
