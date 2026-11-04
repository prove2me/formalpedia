-- Prove2me | Theorems.Thm_ThreeSum_StoredReporting_storedQueryValue_eq_prefixQuery_w3sum_ac885d1
-- name    : ThreeSum.StoredReporting.storedQueryValue_eq_prefixQuery_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:13:04.527679+00:00
-- url     : https://prove2.me/theorems/bcf52cd5-ad0e-42fe-819e-3fcf19d8e3c3
-- title:
--   Stored Reporting: stored Query Value eq prefix Query
-- statement:
--   The Stored Reporting construction uses the stored Query Value eq prefix Query property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/StoredReporting.lean#L111-L134
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/StoredReporting.lean#L111-L134

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

theorem ThreeSum.StoredReporting.storedQueryValue_eq_prefixQuery_w3sum_ac885d1 {h J k : ℕ} (P d : ℤ)
    (A : Finset α) (B : Finset β) (C : Finset γ)
    (a : α → ℤ) (b : β → ℤ) (c : γ → ℤ) (w : Wanted h J α)
    (pre : List (Finset (Fin (512 * h)))) (hk : k ≤ J) :
    storedQueryValue P d A B C a b c w k pre =
      (prefixQuery (rawOn h J P d (A ×ˢ (B ×ˢ C)) a b c) w k pre : ℕ) := by sorry
