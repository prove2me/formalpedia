-- Prove2me | Theorems.Thm_ThreeSum_LightTernarySourceKeys_meets
-- name    : ThreeSum.LightTernarySourceKeys.meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:28:18.520199+00:00
-- url     : https://prove2.me/theorems/da093ecb-e3fb-4372-8c30-74e0f480f25e
-- title:
--   Light Ternary Source Keys: meets
-- statement:
--   The Light Ternary Source Keys construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernarySourceKeys.lean#L37-L121
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernarySourceKeys.lean#L37-L121

import Definitions.Def_Submission_ThreeSum_LightTernaryLookup
import Definitions.Def_Submission_ThreeSum_LightHistogram
import Definitions.Def_Submission_ThreeSum_LightTernarySourceKeys
import Definitions.Def_WeightedCache3SUM_Alias_d9563e39a04084e5

set_option autoImplicit false
open ThreeSum ThreeSum.LightTernarySourceKeys
open Light ThreeSum.LightSubsetAddress
set_option maxHeartbeats 2000000
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightTernarySourceKeys.meets {pMain pSearch a bank powers W L pairs count words wordCount dst d : ℕ}
    (hmain : P[pMain]? = some (body pSearch))
    (hsearch : P[pSearch]? = some (LightBandLookup.searchBody pSearch))
    (μ : ℕ → ℤ) (codes : ℕ → ℕ) (position key : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (ha : a+bank ≤ dst) (hpair : pairs+2*count ≤ dst)
    (hwords : words+wordCount ≤ dst) (hpows : powers+(W+1) ≤ dst)
    (hdst : dst+count ≤ lim.space)
    (hword : ((bank+2^(W+1)+16 : ℕ) : ℤ) ≤ lim.word)
    (hcodes : ∀ i < bank, μ (a+i) = (codes i : ℤ))
    (hpairRead : ∀ i < count, μ (pairs+2*i+1) = (position i : ℤ))
    (hposition : ∀ i < count, position i < wordCount)
    (hwordRead : ∀ i < count, μ (words+position i) = (codes (key i) : ℤ))
    (hkey : ∀ i < count, key i < bank)
    (hcodeBound : ∀ i < bank, codes i < 2^W)
    (hpowers : Powers μ powers W)
    (hsorted : ∀ i k, i < k → k < bank → codes i < codes k)
    (hL : L ≤ W) (hn : bank < 2^L) (hd : d+L+1 ≤ lim.depth) :
    Meets lim P pMain d [a,bank,powers,L,pairs,count,words,wordCount,dst] μ
      (time L count) (fun _ μ' =>
        (∀ i < count, μ' (dst+i) = (key i : ℤ)) ∧ SameOutside μ μ' dst count) := by sorry
