-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryLookup_zeta_meets
-- name    : ThreeSum.LightTernaryLookup.zeta_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:39:45.957981+00:00
-- url     : https://prove2.me/theorems/8fbe6e36-98e5-4280-9a48-94c3def66c49
-- title:
--   Light Ternary Lookup: zeta meets
-- statement:
--   Three lower code lookups followed by the actual ternary value kernel.
--   For digits zero/one, irrelevant higher addresses can duplicate a lower code.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryLookup.lean#L59-L103
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryLookup.lean#L59-L103

import Definitions.Def_Submission_ThreeSum_LightBandLookup
import Definitions.Def_Submission_ThreeSum_LightTernaryCell
import Definitions.Def_Submission_ThreeSum_LightTernaryLookup
import Theorems.Thm_ThreeSum_LightTernaryCell_zeta_meets

set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryLookup
open Light ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightTernaryLookup.zeta_meets {pMain pSearch pCell a n powers W L src j0 j1 j2 d U : ℕ}
    (hmain : P[pMain]? = some (body pSearch pCell))
    (hsearch : P[pSearch]? = some (LightBandLookup.searchBody pSearch))
    (hcell : P[pCell]? = some LightTernaryCell.zetaBody)
    (μ : ℕ → ℤ) (codes : ℕ → ℤ) (q : Fin 3) (f : Fin 3 → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (ha : a+n ≤ lim.space) (hsrc : src+n ≤ lim.space)
    (hspace : powers+(W+1) ≤ lim.space)
    (hword : ((n+2^(W+1)+16 : ℕ) : ℤ) ≤ lim.word)
    (hread : ∀ i < n, μ (a+i) = codes i)
    (hpowers : Powers μ powers W)
    (hsorted : ∀ i k, i < k → k < n → codes i < codes k)
    (hj0 : j0 < n) (hj1 : j1 < n) (hj2 : j2 < n)
    (hr0 : μ (src+j0) = f 0) (hr1 : μ (src+j1) = f 1)
    (hr2 : μ (src+j2) = f 2)
    (hf : ∀ e, |f e| ≤ U) (hvalue : 4 * (U : ℤ) + 3 ≤ lim.word)
    (hL : L ≤ W) (hn : n < 2^L) (hd : d+L+1 ≤ lim.depth) :
    Meets lim P pMain d [a,n,powers,L,q.val,codes j0,codes j1,codes j2,src]
      μ (time L) (fun r μ' => r = ThreeSum.TernaryQuery.zetaDigit f q ∧ μ' = μ) := by sorry
