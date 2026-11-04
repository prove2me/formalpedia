-- Prove2me | Theorems.Thm_ThreeSum_LightArray_linear_meets
-- name    : ThreeSum.LightArray.linear_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:21:56.172464+00:00
-- url     : https://prove2.me/theorems/07769007-5f2a-42e1-9cb0-8e72f257f80f
-- title:
--   Light Array: linear meets
-- statement:
--   The Light Array construction uses the linear meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightArray.lean#L42-L62
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightArray.lean#L42-L62

import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Copy
import Definitions.Def_Submission_ThreeSumApsp_Lang_Tactics
import Definitions.Def_Submission_ThreeSum_LightArray
set_option autoImplicit false
open ThreeSum ThreeSum.LightArray
open Light
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightArray.linear_meets {p : ℕ} (hp : P[p]? = some linearBody)
    {μ : ℕ → ℤ} {srcA srcB dst n : ℕ} {c : ℤ}
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hA : srcA + n ≤ lim.space) (hB : srcB + n ≤ lim.space)
    (hD : dst + n ≤ lim.space)
    (hsepA : SourceSafe srcA dst n) (hsepB : SourceSafe srcB dst n)
    (hmul : ∀ i < n, |c * μ (srcB + i)| ≤ lim.word)
    (hsum : ∀ i < n, |μ (srcA + i) + c * μ (srcB + i)| ≤ lim.word) :
    Meets lim P p d [(srcA : ℤ), srcB, dst, n, c] μ (linearTime n) fun _ μ' =>
      (∀ i < n, μ' (dst + i) = μ (srcA + i) + c * μ (srcB + i)) ∧
        SameOutside μ μ' dst n := by sorry
