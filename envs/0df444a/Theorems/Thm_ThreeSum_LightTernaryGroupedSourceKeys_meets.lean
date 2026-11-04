-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryGroupedSourceKeys_meets
-- name    : ThreeSum.LightTernaryGroupedSourceKeys.meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:28:17.884915+00:00
-- url     : https://prove2.me/theorems/cea423c6-7fdf-4c4c-ab55-6462fba665ec
-- title:
--   Light Ternary Grouped Source Keys: meets
-- statement:
--   The Light Ternary Grouped Source Keys construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryGroupedSourceKeys.lean#L37-L148
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryGroupedSourceKeys.lean#L37-L148

import Definitions.Def_Submission_ThreeSum_LightTernaryLookup
import Definitions.Def_Submission_ThreeSum_LightHistogram
import Definitions.Def_Submission_ThreeSum_LightTernaryGroupedSourceKeys
import Definitions.Def_WeightedCache3SUM_Alias_d9563e39a04084e5

set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryGroupedSourceKeys
open Light ThreeSum.LightSubsetAddress
set_option maxHeartbeats 2000000
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightTernaryGroupedSourceKeys.meets {pMain pSearch a bank powers W L pairs count words wordCount dst groupBase groups d : ℕ}
    (hmain : P[pMain]? = some (body pSearch))
    (hsearch : P[pSearch]? = some (LightBandLookup.searchBody pSearch))
    (μ : ℕ → ℤ) (codes : ℕ → ℕ) (position key group : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (ha : a+bank ≤ dst) (hpair : pairs+2*count ≤ dst)
    (hwords : words+wordCount ≤ dst) (hpows : powers+(W+1) ≤ dst)
    (hgroups : groupBase+wordCount ≤ dst)
    (hgroupRead : ∀ i < count, μ (groupBase+position i) = (group i : ℤ))
    (hgroupLt : ∀ i < count, group i < groups)
    (hgroupWord : ((groups*bank+1 : ℕ) : ℤ) ≤ lim.word)
    (hgroupSpace : groups*bank+1 ≤ lim.space)
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
    Meets lim P pMain d [a,bank,powers,L,pairs,count,words,wordCount,dst,groupBase,groups] μ
      (time L count) (fun _ μ' =>
        (∀ i < count, μ' (dst+i) = ((group i*bank+key i : ℕ) : ℤ)) ∧ SameOutside μ μ' dst count) := by sorry
