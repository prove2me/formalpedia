-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryLookup_code_meets
-- name    : ThreeSum.LightTernaryLookup.code_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:34:22.259772+00:00
-- url     : https://prove2.me/theorems/bc15fe87-07dd-4ceb-8cf6-2c3f226fb034
-- title:
--   Light Ternary Lookup: code meets
-- statement:
--   The Light Ternary Lookup construction uses the code meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryLookup.lean#L31-L44
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryLookup.lean#L31-L44

import Definitions.Def_Submission_ThreeSum_LightBandLookup
import Definitions.Def_Submission_ThreeSum_LightTernaryCell
import Definitions.Def_Submission_ThreeSum_LightTernaryLookup
set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryLookup
open Light ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightTernaryLookup.code_meets {pSearch a n powers W L j d : ℕ}
    (hprog : P[pSearch]? = some (LightBandLookup.searchBody pSearch))
    (μ : ℕ → ℤ) (f : ℕ → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (ha : a+n ≤ lim.space) (hspace : powers+(W+1) ≤ lim.space)
    (hword : ((n+2^(W+1)+16 : ℕ) : ℤ) ≤ lim.word)
    (hread : ∀ i < n, μ (a+i) = f i)
    (hpowers : Powers μ powers W)
    (hsorted : ∀ i k, i < k → k < n → f i < f k)
    (hj : j < n) (hL : L ≤ W) (hn : n < 2^L) (hd : d+L ≤ lim.depth) :
    Meets lim P pSearch d [a,n,f j,powers,L,0] μ (LightBandLookup.searchTime L)
      (fun r μ' => r = ((j+1 : ℕ) : ℤ) ∧ μ' = μ) := by sorry
