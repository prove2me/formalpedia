-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryScalarChannel_power_meets
-- name    : ThreeSum.LightTernaryScalarChannel.power_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:56:54.377339+00:00
-- url     : https://prove2.me/theorems/9748d21f-8977-4472-9262-c21583836ee9
-- title:
--   Light Ternary Scalar Channel: power meets
-- statement:
--   The Light Ternary Scalar Channel construction uses the power meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryScalarChannel.lean#L66-L74
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryScalarChannel.lean#L66-L74

import Definitions.Def_Submission_ThreeSum_TernaryWeightChannels
import Definitions.Def_Submission_ThreeSum_LightArray
import Definitions.Def_Submission_ThreeSum_LightTernaryScalarChannel
set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryScalarChannel
open Light LightFixedArithmetic TernaryWeightChannels
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightTernaryScalarChannel.power_meets {k p src n dst U : ℕ}
    (hmain : P[p]?=some (body (scalarPower k))) (μ : ℕ→ℤ) (f : ℕ→ℤ)
    (hw : (lim.space : ℤ)≤lim.word) (hsrc : src+n≤lim.space) (hdst : dst+n≤lim.space)
    (hsep : LightArray.SourceSafe src dst n)
    (hread : ∀ i<n, μ (src+i)=f i) (hf : ∀ i<n, |f i|≤(U : ℤ))
    (hword : max (U : ℤ) ((scalarPower k).bound U)≤lim.word) :
    Meets lim P p d [src,n,dst] μ (time (scalarPower k) n)
      (fun _ ν => (∀ i<n, ν (dst+i)=(f i)^k) ∧ SameOutside μ ν dst n) := by sorry
