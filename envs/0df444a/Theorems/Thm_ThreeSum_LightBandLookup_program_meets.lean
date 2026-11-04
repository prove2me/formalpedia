-- Prove2me | Theorems.Thm_ThreeSum_LightBandLookup_program_meets
-- name    : ThreeSum.LightBandLookup.program_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:29:33.289197+00:00
-- url     : https://prove2.me/theorems/e2ade04e-c316-4074-b2b0-d0f6206c4d47
-- title:
--   Light Band Lookup: program meets
-- statement:
--   The Light Band Lookup construction uses the program meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBandLookup.lean#L196-L209
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBandLookup.lean#L196-L209

import Definitions.Def_Submission_ThreeSum_BinarySearch
import Definitions.Def_Submission_ThreeSum_LightSubsetAddress
import Definitions.Def_Submission_ThreeSum_LightBandLookup
set_option autoImplicit false
open ThreeSum ThreeSum.LightBandLookup
open Light ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightBandLookup.program_meets {a b n powers W L d : ℕ} {x : ℤ}
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
    Meets lim program 0 d [a,b,n,x,powers,L] μ (time L)
      (fun r μ' => r = (result lo hi n x : ℤ) ∧ μ' = μ) := by sorry
