-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryTaggedChannel_meets
-- name    : ThreeSum.LightTernaryTaggedChannel.meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:37:15.891255+00:00
-- url     : https://prove2.me/theorems/e68ae837-6ce4-4b45-9edc-4ddc351c797e
-- title:
--   Light Ternary Tagged Channel: meets
-- statement:
--   The Light Ternary Tagged Channel construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryTaggedChannel.lean#L35-L71
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryTaggedChannel.lean#L35-L71

import Definitions.Def_Submission_ThreeSum_TernarySignedLayout
import Definitions.Def_Submission_ThreeSum_LightTernaryProductChannel
import Definitions.Def_Submission_ThreeSum_LightTernaryTaggedChannel
import Definitions.Def_WeightedCache3SUM_Alias_d7235e9f603abd3f
import Theorems.Thm_ThreeSum_LightFiniteTable_meets
import Definitions.Def_WeightedCache3SUM_Alias_737c7144994f79de
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c
import Definitions.Def_WeightedCache3SUM_Alias_54f2bf19dfb01d66
import Definitions.Def_WeightedCache3SUM_Alias_9a4576158068ee52
import Theorems.Thm_ThreeSum_LightSignedFiniteTable_meets
import Theorems.Thm_ThreeSum_LightTernaryProductChannel_meets
import Theorems.Thm_ThreeSum_LightTernarySignedRow_Procs_meets
import Theorems.Thm_ThreeSum_LightTernaryWeightedHistogram_meets

set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryTaggedChannel
open Light TernarySignedLayout
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightTernaryTaggedChannel.meets {pMain pOffset pProduct src n J a b dst U : ℕ}
    (hmain : P[pMain]?=some (body pOffset pProduct))
    (hoffset : P[pOffset]?=some offsetBody)
    (hproduct : P[pProduct]?=some LightTernaryProductChannel.body)
    (μ : ℕ→ℤ) (F : ℕ→ℕ→ℤ)
    (hw : (lim.space : ℤ)≤lim.word) (hd : d<lim.depth)
    (ha : a<J+2) (hb : b<J+2)
    (hsrc : src+n*(J+2)≤dst) (hdst : dst+n≤lim.space)
    (hread : ∀ i<n, ∀ j<J+2, μ (src+i*(J+2)+offset J j)=F i j)
    (hf : ∀ i<n, ∀ j<J+2, |F i j|≤(U : ℤ))
    (hword : ((U : ℤ)+1)^2≤lim.word)
    (hindex : ((J+3 : ℕ) : ℤ)≤lim.word) :
    Meets lim P pMain d [src,n,J,a,b,dst] μ (time n)
      (fun _ ν => (∀ i<n, ν (dst+i)=F i a*F i b) ∧ SameOutside μ ν dst n) := by sorry
