-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryTensorScatter_meets
-- name    : ThreeSum.LightTernaryTensorScatter.meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:24:37.685554+00:00
-- url     : https://prove2.me/theorems/00c29eb6-372d-49fb-869b-ed6bb51bcdc5
-- title:
--   Light Ternary Tensor Scatter: meets
-- statement:
--   The Light Ternary Tensor Scatter construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryTensorScatter.lean#L29-L76
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryTensorScatter.lean#L29-L76

import Definitions.Def_Submission_ThreeSum_LightArray
import Definitions.Def_Submission_ThreeSum_LightTernaryTensorScatter
set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryTensorScatter
open Light
set_option maxHeartbeats 1800000

theorem ThreeSum.LightTernaryTensorScatter.meets {lim : Limits} {P : Program} {p d src dst n W q : ℕ}
    (hmain : P[p]?=some body) (μ : ℕ→ℤ)
    (hw : (lim.space : ℤ)≤lim.word) (hW : 0<W) (hq : q<W)
    (hsrc : src+n≤lim.space) (hdst : dst+n*W≤lim.space)
    (hsep : Apart src n dst (n*W))
    (hWWord : (W : ℤ)≤lim.word) (hnWord : (n : ℤ)≤lim.word) :
    Meets lim P p d [src,dst,n,W,q] μ (time n)
      (fun _ ν => (∀ j<n, ν (dst+j*W+q)=μ (src+j)) ∧
        (∀ x, (∀ j<n, x≠dst+j*W+q)→ν x=μ x)) := by sorry
