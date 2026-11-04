-- Prove2me | Theorems.Thm_ThreeSum_LightBandTable_row_meets_w3sum_ac885d1
-- name    : ThreeSum.LightBandTable.row_meets_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:11:23.599112+00:00
-- url     : https://prove2.me/theorems/955c464b-72ff-47e6-bc99-e7c57271416b
-- title:
--   Light Band Table: row meets
-- statement:
--   The Light Band Table construction uses the row meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBandTable.lean#L31-L105
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBandTable.lean#L31-L105

import Definitions.Def_Submission_ThreeSum_LightBandLookup
import Definitions.Def_Submission_ThreeSum_LightBandTable
import Theorems.Thm_ThreeSum_LightPascal_row_meets

set_option autoImplicit false
open ThreeSum ThreeSum.LightBandTable
open Light ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightBandTable.row_meets_w3sum_ac885d1 {pRow pLookup pSearch b loBase hiBase n m dst powers W d U : ℕ}
    {x s : ℤ} (hrow : P[pRow]? = some (rowBody pLookup))
    (hlookup : P[pLookup]? = some (LightBandLookup.body pSearch))
    (hsearch : P[pSearch]? = some (LightBandLookup.searchBody pSearch))
    (μ : ℕ → ℤ) (f lo hi : ℕ → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hb : b+n ≤ dst) (hlo : loBase+m ≤ dst) (hhi : hiBase+m ≤ dst)
    (hdst : dst+n ≤ powers) (hspace : powers+(W+1) ≤ lim.space)
    (hword : ((m+2^(W+1)+16 : ℕ) : ℤ) ≤ lim.word)
    (hqueryWord : 2*(U : ℤ) ≤ lim.word)
    (hread : ∀ j < n, μ (b+j) = f j)
    (hreadLo : ∀ j < m, μ (loBase+j) = lo j)
    (hreadHi : ∀ j < m, μ (hiBase+j) = hi j)
    (hpowers : Powers μ powers W)
    (hsorted : ∀ i j, i ≤ j → j < m → lo i ≤ lo j)
    (hm : m < 2^W) (hs : |s| ≤ 1) (hx : |x| ≤ U)
    (hf : ∀ j < n, |f j| ≤ U) (hd : d+W+2 ≤ lim.depth) :
    Meets lim P pRow d [x,b,loBase,hiBase,n,m,dst,powers,W,s] μ (rowTime n W)
      (fun _ μ' =>
        (∀ j < n, μ' (dst+j) = (rowValue lo hi m x s f j : ℤ)) ∧
        SameOutside μ μ' dst n) := by sorry
