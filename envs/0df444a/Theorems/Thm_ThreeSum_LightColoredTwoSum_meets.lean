-- Prove2me | Theorems.Thm_ThreeSum_LightColoredTwoSum_meets
-- name    : ThreeSum.LightColoredTwoSum.meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:28:23.459131+00:00
-- url     : https://prove2.me/theorems/6aa7aa9e-82ae-41b6-a766-cbe08d5bd692
-- title:
--   Light Colored Two Sum: meets
-- statement:
--   The Light Colored Two Sum construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightColoredTwoSum.lean#L69-L147
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightColoredTwoSum.lean#L69-L147

import Definitions.Def_Submission_ThreeSum_LightBandLookup
import Definitions.Def_Submission_ThreeSum_LightColoredTwoSum
import Definitions.Def_WeightedCache3SUM_Alias_d9563e39a04084e5

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightColoredTwoSum
open Light ThreeSum.LightSubsetAddress
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 4000000
set_option maxRecDepth 12000
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightColoredTwoSum.meets {pMain pLookup pSearch a n b m powers W L U d : ℕ} (bad sign : ℤ)
    (hmain : P[pMain]?=some (body pLookup))
    (hlookup : P[pLookup]?=some (LightBandLookup.body pSearch))
    (hsearch : P[pSearch]?=some (LightBandLookup.searchBody pSearch))
    (μ : ℕ → ℤ) (scan target : ℕ → ℤ)
    (hw : (lim.space : ℤ)≤lim.word) (ha : a+n≤lim.space) (hb : b+m≤lim.space)
    (hspace : powers+(W+1)≤lim.space)
    (hword : ((m+2^(W+1)+16 : ℕ) : ℤ)≤lim.word)
    (hvalues : ∀ i<n, |scan i|≤U) (hbad : |bad|≤U) (hsign : |sign|≤1)
    (hvalueWord : 2*(U : ℤ)+3≤lim.word)
    (hread : ∀ i<n, μ (a+i)=scan i) (htarget : ∀ j<m, μ (b+j)=target j)
    (hpowers : Powers μ powers W)
    (hsorted : ∀ i j, i<j → j<m → target i<target j)
    (hL : L≤W) (hm : m<2^L) (hd : d+L+2≤lim.depth) :
    Meets lim P pMain d [a,n,b,m,powers,L,bad,sign] μ (time n L)
      (fun r ν => r=(flag scan target m n bad sign : ℤ) ∧ ν=μ) := by sorry
