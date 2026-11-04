-- Prove2me | Theorems.Thm_ThreeSum_LightTernarySourceHistogram_meets
-- name    : ThreeSum.LightTernarySourceHistogram.meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:37:17.081426+00:00
-- url     : https://prove2.me/theorems/564b6e3f-6dec-4923-b4fa-e73feeb49745
-- title:
--   Light Ternary Source Histogram: meets
-- statement:
--   The Light Ternary Source Histogram construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernarySourceHistogram.lean#L55-L110
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernarySourceHistogram.lean#L55-L110

import Definitions.Def_Submission_ThreeSum_LightTernarySourceKeys
import Definitions.Def_Submission_ThreeSum_LightTernarySourceHistogram
import Definitions.Def_WeightedCache3SUM_Alias_d9563e39a04084e5
import Theorems.Thm_ThreeSum_LightTernarySourceKeys_meets

set_option autoImplicit false
open ThreeSum ThreeSum.LightTernarySourceHistogram
open Light ThreeSum.LightArray ThreeSum.LightSubsetAddress
set_option maxHeartbeats 2000000
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightTernarySourceHistogram.meets {pMain pKeys pHist pScale pSearch pFill a bank powers W L
    pairs count words wordCount keyBase valueBase : ℕ}
    (hmain : P[pMain]? = some (body pKeys pHist pScale))
    (hkeys : P[pKeys]? = some (LightTernarySourceKeys.body pSearch))
    (hsearch : P[pSearch]? = some (LightBandLookup.searchBody pSearch))
    (hhist : P[pHist]? = some (LightHistogram.histogramBody pFill))
    (hfill : P[pFill]? = some fillBody) (hscale : P[pScale]? = some scaleBody)
    (μ : ℕ → ℤ) (codes : ℕ → ℕ) (position key : ℕ → ℕ) (weight : ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (ha : a+bank ≤ keyBase) (hpair : pairs+2*count ≤ keyBase)
    (hwords : words+wordCount ≤ keyBase) (hpows : powers+(W+1) ≤ keyBase)
    (hkeysBefore : keyBase+count ≤ valueBase) (hvalues : valueBase+bank ≤ lim.space)
    (hword : ((bank+2^(W+1)+16 : ℕ) : ℤ) ≤ lim.word)
    (hweight : (weight : ℤ) ≤ lim.word)
    (hweightedCount : (weight : ℤ)*(count : ℤ) ≤ lim.word)
    (hcodes : ∀ i < bank, μ (a+i) = (codes i : ℤ))
    (hpairRead : ∀ i < count, μ (pairs+2*i+1) = (position i : ℤ))
    (hposition : ∀ i < count, position i < wordCount)
    (hwordRead : ∀ i < count, μ (words+position i) = (codes (key i) : ℤ))
    (hkey : ∀ i < count, key i < bank)
    (hcodeBound : ∀ i < bank, codes i < 2^W)
    (hpowers : Powers μ powers W)
    (hsorted : ∀ i k, i < k → k < bank → codes i < codes k)
    (hL : L ≤ W) (hn : bank < 2^L) (hd : d+L+2 ≤ lim.depth) :
    Meets lim P pMain d
      [a,bank,powers,L,pairs,count,words,wordCount,keyBase,valueBase,weight] μ
      (time L count bank) (fun _ ν =>
        (∀ r < bank, ν (valueBase+r) =
          (weight : ℤ)*(LightHistogram.count key r count : ℤ)) ∧
        ∀ x, (x < keyBase ∨ keyBase+count ≤ x) →
          (x < valueBase ∨ valueBase+bank ≤ x) → ν x = μ x) := by sorry
