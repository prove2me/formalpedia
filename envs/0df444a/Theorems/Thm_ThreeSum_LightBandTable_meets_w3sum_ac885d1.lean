-- Prove2me | Theorems.Thm_ThreeSum_LightBandTable_meets_w3sum_ac885d1
-- name    : ThreeSum.LightBandTable.meets_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:11:21.083425+00:00
-- url     : https://prove2.me/theorems/875e7278-b933-4b60-8020-226872aebd9d
-- title:
--   Light Band Table: meets
-- statement:
--   The Light Band Table construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBandTable.lean#L116-L206
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBandTable.lean#L116-L206

import Definitions.Def_Submission_ThreeSum_LightBandLookup
import Definitions.Def_Submission_ThreeSum_LightBandTable
import Definitions.Def_WeightedCache3SUM_Alias_d9563e39a04084e5

set_option autoImplicit false
open ThreeSum ThreeSum.LightBandTable
open Light ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightBandTable.meets_w3sum_ac885d1 {pMain pRow pLookup pSearch a b loBase hiBase nX nY m dst powers W d U : ℕ}
    {s : ℤ} (hmain : P[pMain]? = some (body pRow))
    (hrow : P[pRow]? = some (rowBody pLookup))
    (hlookup : P[pLookup]? = some (LightBandLookup.body pSearch))
    (hsearch : P[pSearch]? = some (LightBandLookup.searchBody pSearch))
    (μ : ℕ → ℤ) (f g lo hi : ℕ → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (ha : a+nX ≤ dst) (hb : b+nY ≤ dst)
    (hlo : loBase+m ≤ dst) (hhi : hiBase+m ≤ dst)
    (hdst : dst+nX*nY ≤ powers) (hspace : powers+(W+1) ≤ lim.space)
    (hword : ((m+2^(W+1)+16 : ℕ) : ℤ) ≤ lim.word)
    (hqueryWord : 2*(U : ℤ) ≤ lim.word)
    (hreadA : ∀ i < nX, μ (a+i) = f i)
    (hreadB : ∀ j < nY, μ (b+j) = g j)
    (hreadLo : ∀ j < m, μ (loBase+j) = lo j)
    (hreadHi : ∀ j < m, μ (hiBase+j) = hi j)
    (hpowers : Powers μ powers W)
    (hsorted : ∀ i j, i ≤ j → j < m → lo i ≤ lo j)
    (hm : m < 2^W) (hs : |s| ≤ 1)
    (hf : ∀ i < nX, |f i| ≤ U) (hg : ∀ j < nY, |g j| ≤ U)
    (hd : d+W+3 ≤ lim.depth) :
    Meets lim P pMain d [a,b,loBase,hiBase,nX,nY,m,dst,powers,W,s] μ (time nX nY W)
      (fun _ μ' =>
        (∀ i < nX, ∀ j < nY,
          μ' (dst+i*nY+j) = (rowValue lo hi m (f i) s g j : ℤ)) ∧
        SameOutside μ μ' dst (nX*nY)) := by sorry
