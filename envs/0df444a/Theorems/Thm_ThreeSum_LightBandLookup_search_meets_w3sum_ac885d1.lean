-- Prove2me | Theorems.Thm_ThreeSum_LightBandLookup_search_meets_w3sum_ac885d1
-- name    : ThreeSum.LightBandLookup.search_meets_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:08:57.420069+00:00
-- url     : https://prove2.me/theorems/94c921bf-6b93-4b53-b76d-0569619fbfd9
-- title:
--   Light Band Lookup: search meets
-- statement:
--   The Light Band Lookup construction uses the search meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBandLookup.lean#L35-L126
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBandLookup.lean#L35-L126

import Definitions.Def_Submission_ThreeSum_BinarySearch
import Definitions.Def_Submission_ThreeSum_LightSubsetAddress
import Definitions.Def_Submission_ThreeSum_LightBandLookup
set_option autoImplicit false
open ThreeSum ThreeSum.LightBandLookup
open Light ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightBandLookup.search_meets_w3sum_ac885d1 {pSearch a n powers W : ℕ} {x : ℤ}
    (hprog : P[pSearch]? = some (searchBody pSearch))
    (μ : ℕ → ℤ) (f : ℕ → ℤ) (K : ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (ha : a+n ≤ lim.space) (hspace : powers+(W+1) ≤ lim.space)
    (hword : ((n+2^(W+1)+16 : ℕ) : ℤ) ≤ lim.word)
    (hread : ∀ i < n, μ (a+i) = f i)
    (hpowers : Powers μ powers W)
    (hpart : BinarySearch.Partition f x n K) :
    ∀ L k : ℕ, L ≤ W → k ≤ K → K < k+2^L →
      ∀ d, d+L ≤ lim.depth →
      Meets lim P pSearch d [a,n,x,powers,L,k] μ (searchTime L)
        (fun r μ' => r = (K : ℤ) ∧ μ' = μ) := by sorry
