-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryGroupedSources_meets
-- name    : ThreeSum.LightTernaryGroupedSources.meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:47:14.38343+00:00
-- url     : https://prove2.me/theorems/f416a987-dde8-41fe-a095-dbbea0c27ae2
-- title:
--   Light Ternary Grouped Sources: meets
-- statement:
--   The Light Ternary Grouped Sources construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryGroupedSources.lean#L24-L107
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryGroupedSources.lean#L24-L107

import Definitions.Def_Submission_ThreeSum_LightTernarySourceHistogram
import Definitions.Def_Submission_ThreeSum_LightTernaryGroupedSourceKeys
import Definitions.Def_Submission_ThreeSum_TernaryWeightedPhysicalSources
import Definitions.Def_Submission_ThreeSum_LightTernaryGroupedSources
import Definitions.Def_WeightedCache3SUM_Alias_d9563e39a04084e5
import Theorems.Thm_ThreeSum_LightTernaryGroupedSourceKeys_meets
import Theorems.Thm_ThreeSum_LightTernarySourceHistogram_meets
import Theorems.Thm_ThreeSum_LightTernarySourceKeys_meets
import Theorems.Thm_ThreeSum_LightTernaryWeightedHistogram_meets

set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryGroupedSources
open Light ThreeSum.LightSubsetAddress
set_option maxHeartbeats 3000000
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightTernaryGroupedSources.meets {pMain pKeys pHist pScale pSearch pFill a bank powers W L
    pairs count words wordCount keyBase valueBase weightBase originalCount U groupBase groups : ℕ}
    (hmain : P[pMain]?=some (body pKeys pHist pScale))
    (hkeys : P[pKeys]?=some (LightTernaryGroupedSourceKeys.body pSearch))
    (hsearch : P[pSearch]?=some (LightBandLookup.searchBody pSearch))
    (hhist : P[pHist]?=some (LightTernaryWeightedHistogram.body pFill))
    (hfill : P[pFill]?=some fillBody)
    (hscale : P[pScale]?=some LightTernarySourceHistogram.scaleBody)
    (μ : ℕ → ℤ) (codes : ℕ → ℕ) (dictionaryPosition originalPosition key group : ℕ → ℕ)
    (weight : ℕ → ℤ) (factor : ℕ)
    (hw : (lim.space : ℤ)≤lim.word)
    (ha : a+bank≤keyBase) (hpair : pairs+2*count≤keyBase)
    (hwords : words+wordCount≤keyBase) (hpows : powers+(W+1)≤keyBase)
    (hweightArray : weightBase+originalCount≤keyBase)
    (hgroupArray : groupBase+wordCount≤keyBase)
    (hgroupRead : ∀ i<count, μ (groupBase+dictionaryPosition i)=(group i : ℤ))
    (hgroupLt : ∀ i<count, group i<groups)
    (hgroupWord : ((groups*bank+1 : ℕ) : ℤ)≤lim.word)
    (hgroupSpace : groups*bank+1≤lim.space)
    (hkeysBefore : keyBase+count≤valueBase) (hvalues : valueBase+groups*bank≤lim.space)
    (hword : ((bank+2^(W+1)+16 : ℕ) : ℤ)≤lim.word)
    (hfactor : (factor : ℤ)≤lim.word)
    (hweightedCount : (factor : ℤ)*(count*U : ℕ)≤lim.word)
    (hhistWord : ((count+1 : ℕ) : ℤ)*U≤lim.word)
    (hcodes : ∀ i<bank, μ (a+i)=(codes i : ℤ))
    (hpairRead : ∀ i<count, μ (pairs+2*i+1)=(dictionaryPosition i : ℤ))
    (hdictionaryPosition : ∀ i<count, dictionaryPosition i<wordCount)
    (hwordRead : ∀ i<count, μ (words+dictionaryPosition i)=(codes (key i) : ℤ))
    (hkey : ∀ i<count, key i<bank)
    (hcodeBound : ∀ i<bank, codes i<2^W)
    (hpowers : Powers μ powers W)
    (hsorted : ∀ i k, i<k → k<bank → codes i<codes k)
    (hposRead : ∀ i<count, μ (pairs+2*i)=(originalPosition i : ℤ))
    (hposLt : ∀ i<count, originalPosition i<originalCount)
    (hweightRead : ∀ i<count, μ (weightBase+originalPosition i)=weight i)
    (hweightBound : ∀ i<count, |weight i|≤U)
    (hL : L≤W) (hn : bank<2^L) (hd : d+L+2≤lim.depth) :
    Meets lim P pMain d
      [a,bank,powers,L,pairs,count,words,wordCount,keyBase,valueBase,
        weightBase,originalCount,factor,groupBase,groups] μ (time L count bank groups)
      (fun _ ν => (∀ r<groups*bank, ν (valueBase+r)=
        (factor : ℤ)*LightTernaryWeightedHistogram.total (fun i => group i*bank+key i) weight r count) ∧
        ∀ x, (x<keyBase ∨ keyBase+count≤x) →
          (x<valueBase ∨ valueBase+groups*bank≤x) → ν x=μ x) := by sorry
