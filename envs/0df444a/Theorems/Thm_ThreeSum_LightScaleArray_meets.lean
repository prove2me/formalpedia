-- Prove2me | Theorems.Thm_ThreeSum_LightScaleArray_meets
-- name    : ThreeSum.LightScaleArray.meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:23:48.028989+00:00
-- url     : https://prove2.me/theorems/8fc29336-9065-4d37-ad56-6aa7f9411228
-- title:
--   Light Scale Array: meets
-- statement:
--   The Light Scale Array construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightScaleArray.lean#L15-L28
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightScaleArray.lean#L15-L28

import Definitions.Def_Submission_ThreeSum_LightArray
import Definitions.Def_Submission_ThreeSum_LightScaleArray
set_option autoImplicit false
open ThreeSum ThreeSum.LightScaleArray
open Light ThreeSum.LightArray
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightScaleArray.meets {p src dst n : ℕ} {c : ℤ} {μ : ℕ → ℤ}
    (hp : P[p]? = some body)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hsrc : src+n ≤ lim.space) (hdst : dst+n ≤ lim.space)
    (hsep : SourceSafe src dst n)
    (hword : ∀ i < n, |c*μ (src+i)| ≤ lim.word) :
    Meets lim P p d [src,dst,n,c] μ (time n)
      (fun _ μ' => (∀ i < n, μ' (dst+i) = c*μ (src+i)) ∧ SameOutside μ μ' dst n) := by sorry
