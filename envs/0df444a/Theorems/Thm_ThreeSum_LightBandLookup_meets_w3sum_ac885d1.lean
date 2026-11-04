-- Prove2me | Theorems.Thm_ThreeSum_LightBandLookup_meets_w3sum_ac885d1
-- name    : ThreeSum.LightBandLookup.meets_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:08:46.471936+00:00
-- url     : https://prove2.me/theorems/b6dd50b7-6ad5-4ac1-adaa-d2ddc11a17e0
-- title:
--   Light Band Lookup: meets
-- statement:
--   The Light Band Lookup construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBandLookup.lean#L152-L192
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBandLookup.lean#L152-L192

import Definitions.Def_Submission_ThreeSum_BinarySearch
import Definitions.Def_Submission_ThreeSum_LightSubsetAddress
import Definitions.Def_Submission_ThreeSum_LightBandLookup
set_option autoImplicit false
open ThreeSum ThreeSum.LightBandLookup
open Light ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightBandLookup.meets_w3sum_ac885d1 {pMain pSearch a b n powers W L d : ℕ} {x : ℤ}
    (hmain : P[pMain]? = some (body pSearch))
    (hsearch : P[pSearch]? = some (searchBody pSearch))
    (μ : ℕ → ℤ) (lo hi : ℕ → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (ha : a+n ≤ lim.space) (hb : b+n ≤ lim.space)
    (hspace : powers+(W+1) ≤ lim.space)
    (hword : ((n+2^(W+1)+16 : ℕ) : ℤ) ≤ lim.word)
    (hreadLo : ∀ i < n, μ (a+i) = lo i)
    (hreadHi : ∀ i < n, μ (b+i) = hi i)
    (hpowers : Powers μ powers W)
    (hsorted : ∀ i j, i ≤ j → j < n → lo i ≤ lo j)
    (hL : L ≤ W) (hn : n < 2^L) (hd : d+L+1 ≤ lim.depth) :
    Meets lim P pMain d [a,b,n,x,powers,L] μ (time L)
      (fun r μ' => r = (result lo hi n x : ℤ) ∧ μ' = μ) := by sorry
