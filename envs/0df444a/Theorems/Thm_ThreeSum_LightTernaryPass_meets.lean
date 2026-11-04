-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryPass_meets
-- name    : ThreeSum.LightTernaryPass.meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:28:15.270661+00:00
-- url     : https://prove2.me/theorems/42508ddf-2e19-47ff-87fb-91fc4347209e
-- title:
--   Light Ternary Pass: meets
-- statement:
--   The Light Ternary Pass construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryPass.lean#L61-L167
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryPass.lean#L61-L167

import Definitions.Def_Submission_ThreeSum_LightTernaryLookup
import Definitions.Def_Submission_ThreeSum_LightTernaryPass
import Definitions.Def_WeightedCache3SUM_Alias_d9563e39a04084e5

set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryPass
set_option maxHeartbeats 2000000
open Light ThreeSum.TernaryQuery ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightTernaryPass.meets {pMain pCell pSearch pValue a n powers W L keyBase src dst d U : ℕ}
    (hmain : P[pMain]? = some (body pCell))
    (hcell : P[pCell]? = some (LightTernaryLookup.body pSearch pValue))
    (hsearch : P[pSearch]? = some (LightBandLookup.searchBody pSearch))
    (hvalue : P[pValue]? = some LightTernaryCell.zetaBody)
    (μ : ℕ → ℤ) (codes f : ℕ → ℤ) (digits : ℕ → Fin 3)
    (ix : Fin 3 → ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (ha : a+n ≤ dst) (hsrc : src+n ≤ dst)
    (hmeta : keyBase+4*n ≤ dst) (hpows : powers+(W+1) ≤ dst)
    (hdst : dst+n ≤ lim.space)
    (hword : ((n+2^(W+1)+16 : ℕ) : ℤ) ≤ lim.word)
    (hcodes : ∀ i < n, μ (a+i) = codes i)
    (hsource : ∀ i < n, μ (src+i) = f i)
    (hpowers : Powers μ powers W)
    (hsorted : ∀ i k, i < k → k < n → codes i < codes k)
    (hindex : ∀ e j, j < n → ix e j < n)
    (hmd : ∀ j < n, μ (keyBase+j) = ((digits j).val : ℤ))
    (hm0 : ∀ j < n, μ (keyBase+n+j) = codes (ix 0 j))
    (hm1 : ∀ j < n, μ (keyBase+2*n+j) = codes (ix 1 j))
    (hm2 : ∀ j < n, μ (keyBase+3*n+j) = codes (ix 2 j))
    (hf : ∀ j < n, |f j| ≤ U) (hvalword : 4*(U : ℤ)+3 ≤ lim.word)
    (hL : L ≤ W) (hn : n < 2^L) (hd : d+L+2 ≤ lim.depth) :
    Meets lim P pMain d [a,n,powers,L,keyBase,src,dst] μ (time L n)
      (fun _ μ' => (∀ j < n, μ' (dst+j) = values digits ix f j) ∧
        SameOutside μ μ' dst n) := by sorry
