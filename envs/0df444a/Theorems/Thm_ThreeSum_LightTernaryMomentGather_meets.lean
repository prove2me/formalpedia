-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryMomentGather_meets
-- name    : ThreeSum.LightTernaryMomentGather.meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:24:40.697758+00:00
-- url     : https://prove2.me/theorems/3a572c7c-2dcd-4a8c-ba20-4e2062894e9a
-- title:
--   Light Ternary Moment Gather: meets
-- statement:
--   The Light Ternary Moment Gather construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryMomentGather.lean#L13-L41
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryMomentGather.lean#L13-L41

import Definitions.Def_Submission_ThreeSum_LightArray
import Definitions.Def_Submission_ThreeSum_LightTernaryMomentGather
set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryMomentGather
open Light
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightTernaryMomentGather.meets {p matrix count row scratch terms U : ℕ}
    (hmain : P[p]?=some body) (μ : ℕ→ℤ) (M : ℕ→ℤ)
    (hw : (lim.space : ℤ)≤lim.word) (hr : row<count)
    (hbefore : matrix+terms*count≤scratch) (hspace : scratch+terms≤lim.space)
    (hread : ∀ k<terms, μ (matrix+k*count+row)=M k)
    (hbound : ∀ k<terms, |M k|≤(U : ℤ)) (hword : (U : ℤ)≤lim.word) :
    Meets lim P p d [matrix,count,row,scratch,terms] μ (time terms)
      (fun _ ν => (∀ k<terms, ν (scratch+k)=M k) ∧ SameOutside μ ν scratch terms) := by sorry
