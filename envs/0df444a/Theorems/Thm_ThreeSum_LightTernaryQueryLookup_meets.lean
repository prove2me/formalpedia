-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryQueryLookup_meets
-- name    : ThreeSum.LightTernaryQueryLookup.meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:28:14.367447+00:00
-- url     : https://prove2.me/theorems/ade8b60d-8885-4e97-8e1c-c16298e54801
-- title:
--   Light Ternary Query Lookup: meets
-- statement:
--   The Light Ternary Query Lookup construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryQueryLookup.lean#L26-L73
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryQueryLookup.lean#L26-L73

import Definitions.Def_Submission_ThreeSum_LightTernaryLookup
import Definitions.Def_Submission_ThreeSum_LightTernaryQueryLookup
import Definitions.Def_WeightedCache3SUM_Alias_d9563e39a04084e5

set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryQueryLookup
open Light ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightTernaryQueryLookup.meets {pMain pSearch a n powers W L src stage j d U : ℕ}
    (hmain : P[pMain]? = some (body pSearch))
    (hsearch : P[pSearch]? = some (LightBandLookup.searchBody pSearch))
    (μ : ℕ → ℤ) (codes : ℕ → ℤ) (value : ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (ha : a+n ≤ lim.space) (hsrc : src+(stage+1)*n ≤ lim.space)
    (hspace : powers+(W+1) ≤ lim.space)
    (hword : ((n+2^(W+1)+16 : ℕ) : ℤ) ≤ lim.word)
    (hread : ∀ i < n, μ (a+i) = codes i)
    (hpowers : Powers μ powers W)
    (hsorted : ∀ i k, i < k → k < n → codes i < codes k)
    (hj : j < n) (hvalue : μ (src+stage*n+j) = value)
    (hval : |value| ≤ U) (hU : (U : ℤ) ≤ lim.word)
    (hL : L ≤ W) (hn : n < 2^L) (hd : d+L+1 ≤ lim.depth) :
    Meets lim P pMain d [a,n,codes j,src,powers,L,stage] μ (time L)
      (fun r μ' => r = value ∧ μ' = μ) := by sorry
