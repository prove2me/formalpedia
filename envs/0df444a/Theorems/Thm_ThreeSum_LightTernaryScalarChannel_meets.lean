-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryScalarChannel_meets
-- name    : ThreeSum.LightTernaryScalarChannel.meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:46:14.829251+00:00
-- url     : https://prove2.me/theorems/da060bc5-670c-476d-add5-f8979beaf26d
-- title:
--   Light Ternary Scalar Channel: meets
-- statement:
--   The Light Ternary Scalar Channel construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryScalarChannel.lean#L14-L49
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryScalarChannel.lean#L14-L49

import Definitions.Def_Submission_ThreeSum_TernaryWeightChannels
import Definitions.Def_Submission_ThreeSum_LightArray
import Definitions.Def_Submission_ThreeSum_LightTernaryScalarChannel
import Theorems.Thm_ThreeSum_LightFiniteTable_meets
import Theorems.Thm_ThreeSum_LightSignedFiniteTable_meets
import Theorems.Thm_ThreeSum_LightTernaryWeightedHistogram_meets

set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryScalarChannel
open Light LightFixedArithmetic TernaryWeightChannels
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightTernaryScalarChannel.meets (e : Circuit) {p src n dst U : ℕ}
    (hmain : P[p]?=some (body e)) (μ : ℕ→ℤ) (f : ℕ→ℤ)
    (hw : (lim.space : ℤ)≤lim.word) (hsrc : src+n≤lim.space) (hdst : dst+n≤lim.space)
    (hsep : LightArray.SourceSafe src dst n)
    (hread : ∀ i<n, μ (src+i)=f i) (hf : ∀ i<n, |f i|≤(U : ℤ))
    (hword : max (U : ℤ) (e.bound U)≤lim.word) :
    Meets lim P p d [src,n,dst] μ (time e n)
      (fun _ ν => (∀ i<n, ν (dst+i)=e.eval (fun _ => f i)) ∧ SameOutside μ ν dst n) := by sorry
