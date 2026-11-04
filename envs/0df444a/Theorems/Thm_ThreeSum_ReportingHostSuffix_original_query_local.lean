-- Prove2me | Theorems.Thm_ThreeSum_ReportingHostSuffix_original_query_local
-- name    : ThreeSum.ReportingHostSuffix.original_query_local
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:20:18.456204+00:00
-- url     : https://prove2.me/theorems/fc0c10b0-4682-458d-be5b-b3c22ca366eb
-- title:
--   Reporting Host Suffix: original query local
-- statement:
--   The Reporting Host Suffix construction uses the original query local property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostSuffix.lean#L136-L149
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostSuffix.lean#L136-L149

import Definitions.Def_Submission_ThreeSum_LightBlockBoxes
import Definitions.Def_Submission_ThreeSum_ReportingHostSuffix
set_option autoImplicit false
open ThreeSum ThreeSum.ReportingHostSuffix
open Finset ThreeSum.SubsetAddress BlockIndexedQuery BlockRows BlockIndex BlockForced
open GlobalEncoding LocalCoverBounds StoredReporting LightBlockQuery
open scoped BigOperators
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]
open RawIncidences RawReporting RawPrefixCounts

theorem ThreeSum.ReportingHostSuffix.original_query_local {h J k : ℕ} (pMod shift : ℤ)
    (A : Finset α) (B : Finset β) (C : Finset γ) (a : α → ℤ) (b : β → ℤ) (c : γ → ℤ)
    (w : Wanted h J α) (pre : List (Finset (Fin (512*h)))) (hk : k ≤ J)
    (hp : ValidPrefix w.2.2 k pre)
    (hkey : w.1 ∈ A ∧ globalModulus h J ∣
      (a w.1 % pMod+lift w.2.1*pMod+shift)-globalKey w.2.2) :
    (-1 : ℤ)^(localQuery hk (outputRows w.2.2)).card *
      ∑ S ∈ (localQuery hk (outputRows w.2.2)).powerset,
        leafWeight (block_fit hk) (leftSource pMod B b w.2.2) (rightSource pMod shift C c w.2.2)
          (suffixStage J (512*h) k) (leftPrefix k (prefixRows (J := J) pre))
          (rightPrefix k (outputRows w.2.2) (prefixRows (J := J) pre)) S =
      (prefixQuery (rawOn h J pMod shift (A ×ˢ (B ×ˢ C)) a b c) w k pre : ℤ) := by sorry
