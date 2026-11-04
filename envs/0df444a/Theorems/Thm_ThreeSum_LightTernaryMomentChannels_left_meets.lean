-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryMomentChannels_left_meets
-- name    : ThreeSum.LightTernaryMomentChannels.left_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:54:32.68343+00:00
-- url     : https://prove2.me/theorems/95095ea1-7a2f-47fe-a97d-89274a7d9581
-- title:
--   Light Ternary Moment Channels: left meets
-- statement:
--   The Light Ternary Moment Channels construction uses the left meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryMomentChannels.lean#L24-L35
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryMomentChannels.lean#L24-L35

import Definitions.Def_Submission_ThreeSum_LightTernaryScalarChannel
import Definitions.Def_Submission_ThreeSum_LightTernaryMomentChannels
set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryMomentChannels
open Light LightFixedArithmetic TernaryWeightChannels
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightTernaryMomentChannels.left_meets {k j p src n dst U : ℕ}
    (hmain : P[p]?=some (LightTernaryScalarChannel.body (leftMoment k j)))
    (μ : ℕ→ℤ) (B : ℕ→ℤ)
    (hw : (lim.space : ℤ)≤lim.word) (hsrc : src+n≤lim.space) (hdst : dst+n≤lim.space)
    (hsep : LightArray.SourceSafe src dst n)
    (hread : ∀ i<n, μ (src+i)=B i) (hB : ∀ i<n, |B i|≤(U : ℤ))
    (hword : max (U : ℤ) (2*((k.choose j : ℤ)+1)*((U : ℤ)+2)^j)≤lim.word) :
    Meets lim P p d [src,n,dst] μ (LightTernaryScalarChannel.time (leftMoment k j) n)
      (fun _ ν => (∀ i<n, ν (dst+i)=(k.choose j : ℤ)*(-(B i))^j) ∧ SameOutside μ ν dst n) := by sorry
