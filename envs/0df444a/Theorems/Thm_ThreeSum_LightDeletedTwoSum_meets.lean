-- Prove2me | Theorems.Thm_ThreeSum_LightDeletedTwoSum_meets
-- name    : ThreeSum.LightDeletedTwoSum.meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:28:59.939423+00:00
-- url     : https://prove2.me/theorems/34a24663-bdd6-4523-aa41-c96431b367ac
-- title:
--   Light Deleted Two Sum: meets
-- statement:
--   The Light Deleted Two Sum construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightDeletedTwoSum.lean#L55-L135
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightDeletedTwoSum.lean#L55-L135

import Definitions.Def_Submission_ThreeSum_LightColoredTwoSum
import Definitions.Def_Submission_ThreeSum_LightOriginalBucketFilter
import Definitions.Def_Submission_ThreeSum_LightDeletedTwoSum
import Definitions.Def_WeightedCache3SUM_Alias_d9563e39a04084e5
import Theorems.Thm_ThreeSum_LightColoredTwoSum_meets
import Theorems.Thm_ThreeSum_LightOriginalBucketFilter_meets

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightDeletedTwoSum
open Light ThreeSum.LightSubsetAddress
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 4000000
set_option maxRecDepth 12000
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightDeletedTwoSum.meets {pMain pTwoSum pLookup pSearch badBase badN valuesBase originalN scanBase scanN targetBase targetN
    powers W L U d : ℕ} (sign : ℤ)
    (hmain : P[pMain]?=some (body pTwoSum))
    (htwo : P[pTwoSum]?=some (LightColoredTwoSum.body pLookup))
    (hlookup : P[pLookup]?=some (LightBandLookup.body pSearch))
    (hsearch : P[pSearch]?=some (LightBandLookup.searchBody pSearch))
    (μ : ℕ → ℤ) (ids : ℕ → ℕ) (values scan target : ℕ → ℤ)
    (hw : (lim.space : ℤ)≤lim.word)
    (hbadSpace : badBase+badN≤lim.space) (hvaluesSpace : valuesBase+originalN≤lim.space)
    (hscanSpace : scanBase+scanN≤lim.space) (htargetSpace : targetBase+targetN≤lim.space)
    (hspace : powers+(W+1)≤lim.space)
    (hword : ((targetN+2^(W+1)+16 : ℕ) : ℤ)≤lim.word)
    (hids : ∀ i<badN, ids i<originalN) (hreadIds : ∀ i<badN, μ (badBase+i)=(ids i : ℤ))
    (hvalues : ∀ i<originalN, |values i|≤U) (hreadValues : ∀ i<originalN, μ (valuesBase+i)=values i)
    (hscan : ∀ i<scanN, |scan i|≤U) (hreadScan : ∀ i<scanN, μ (scanBase+i)=scan i)
    (hreadTarget : ∀ i<targetN, μ (targetBase+i)=target i)
    (hsign : |sign|≤1) (hvalueWord : 2*(U : ℤ)+3≤lim.word)
    (hpowers : Powers μ powers W)
    (hsorted : ∀ i j, i<j → j<targetN → target i<target j)
    (hL : L≤W) (htargetN : targetN<2^L) (hd : d+L+3≤lim.depth) :
    Meets lim P pMain d [badBase,badN,valuesBase,originalN,scanBase,scanN,targetBase,targetN,powers,L,sign] μ
      (time badN scanN L)
      (fun r ν => r=(flag ids values scan target targetN scanN badN sign : ℤ) ∧ ν=μ) := by sorry
