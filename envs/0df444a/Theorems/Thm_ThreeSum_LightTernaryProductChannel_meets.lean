-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryProductChannel_meets
-- name    : ThreeSum.LightTernaryProductChannel.meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:46:07.140327+00:00
-- url     : https://prove2.me/theorems/54c9e8b5-0aba-4afc-9e7c-d4dbfc10cdc6
-- title:
--   Light Ternary Product Channel: meets
-- statement:
--   The Light Ternary Product Channel construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryProductChannel.lean#L14-L55
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryProductChannel.lean#L14-L55

import Definitions.Def_Submission_ThreeSum_LightArray
import Definitions.Def_Submission_ThreeSum_TernaryWeightChannels
import Definitions.Def_Submission_ThreeSum_LightTernaryProductChannel
import Theorems.Thm_ThreeSum_LightFiniteTable_meets
import Theorems.Thm_ThreeSum_LightSignedFiniteTable_meets
import Theorems.Thm_ThreeSum_LightTernaryWeightedHistogram_meets

set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryProductChannel
open Light TernaryWeightChannels
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightTernaryProductChannel.meets {p src n width a b dst U : ℕ}
    (hmain : P[p]?=some body) (μ : ℕ→ℤ) (F : ℕ→ℕ→ℤ)
    (hw : (lim.space : ℤ)≤lim.word) (ha : a<width) (hb : b<width)
    (hsrc : src+n*width≤dst) (hdst : dst+n≤lim.space)
    (hread : ∀ i<n, ∀ j<width, μ (src+i*width+j)=F i j)
    (hf : ∀ i<n, ∀ j<width, |F i j|≤(U : ℤ))
    (hword : ((U : ℤ)+1)^2≤lim.word) :
    Meets lim P p d [src,n,width,a,b,dst] μ (time n)
      (fun _ ν => (∀ i<n, ν (dst+i)=F i a*F i b) ∧ SameOutside μ ν dst n) := by sorry
