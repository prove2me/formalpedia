-- Prove2me | Theorems.Thm_ThreeSum_LightBlockQuery_queryValue_eq_prefixQuery
-- name    : ThreeSum.LightBlockQuery.queryValue_eq_prefixQuery
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:29:52.13823+00:00
-- url     : https://prove2.me/theorems/13bc4389-d141-44d9-87b1-49cb13540fbc
-- title:
--   Light Block Query: query Value eq prefix Query
-- statement:
--   The Light Block Query construction uses the query Value eq prefix Query property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBlockQuery.lean#L34-L47
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBlockQuery.lean#L34-L47

import Definitions.Def_Submission_ThreeSum_BlockIndexedQuery
import Definitions.Def_Submission_ThreeSum_LightSparseQuery
import Definitions.Def_Submission_ThreeSum_LightSignedBoxSetup
import Definitions.Def_Submission_ThreeSum_LightBlockQuery
set_option autoImplicit false
open ThreeSum ThreeSum.LightBlockQuery
open Light Finset ThreeSum.SubsetAddress ThreeSum.LightPascal
open BlockRows BlockForced BlockEncoding BlockIndexedQuery StoredReporting
open GlobalEncoding LocalCoverBounds RawIncidences RawReporting RawPrefixCounts
variable {lim : Limits} {P : Program}
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

theorem ThreeSum.LightBlockQuery.queryValue_eq_prefixQuery {h J k : ℕ} (pMod shift : ℤ)
    (A : Finset α) (B : Finset β) (C : Finset γ)
    (a : α → ℤ) (b : β → ℤ) (c : γ → ℤ) (w : Wanted h J α)
    (pre : List (Finset (Fin (512*h)))) (hk : k ≤ J) (hp : ValidPrefix w.2.2 k pre)
    (hkey : w.1 ∈ A ∧ globalModulus h J ∣
      (a w.1 % pMod + lift w.2.1*pMod + shift)-globalKey w.2.2) :
    queryValue pMod shift B C b c w.2.2 k (prefixRows (J := J) pre) =
      ((prefixQuery (rawOn h J pMod shift (A ×ˢ (B ×ˢ C)) a b c) w k pre : ℕ) : ℤ) := by sorry
