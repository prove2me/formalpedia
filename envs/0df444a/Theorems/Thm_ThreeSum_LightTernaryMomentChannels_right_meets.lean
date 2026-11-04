-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryMomentChannels_right_meets
-- name    : ThreeSum.LightTernaryMomentChannels.right_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:54:25.588697+00:00
-- url     : https://prove2.me/theorems/57ca2f93-5a38-422d-9f0e-da5e1bfcb791
-- title:
--   Light Ternary Moment Channels: right meets
-- statement:
--   The Light Ternary Moment Channels construction uses the right meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryMomentChannels.lean#L37-L48
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryMomentChannels.lean#L37-L48

import Definitions.Def_Submission_ThreeSum_LightTernaryScalarChannel
import Definitions.Def_Submission_ThreeSum_LightTernaryMomentChannels
set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryMomentChannels
open Light LightFixedArithmetic TernaryWeightChannels
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightTernaryMomentChannels.right_meets {k j p src n dst U : ℕ}
    (hmain : P[p]?=some (LightTernaryScalarChannel.body (rightMoment k j)))
    (μ : ℕ→ℤ) (C : ℕ→ℤ)
    (hw : (lim.space : ℤ)≤lim.word) (hsrc : src+n≤lim.space) (hdst : dst+n≤lim.space)
    (hsep : LightArray.SourceSafe src dst n)
    (hread : ∀ i<n, μ (src+i)=C i) (hC : ∀ i<n, |C i|≤(U : ℤ))
    (hword : max (U : ℤ) (2*((U : ℤ)+1)^(k-j))≤lim.word) :
    Meets lim P p d [src,n,dst] μ (LightTernaryScalarChannel.time (rightMoment k j) n)
      (fun _ ν => (∀ i<n, ν (dst+i)=(C i)^(k-j)) ∧ SameOutside μ ν dst n) := by sorry
