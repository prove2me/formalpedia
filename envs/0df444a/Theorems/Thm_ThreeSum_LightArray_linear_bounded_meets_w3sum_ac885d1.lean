-- Prove2me | Theorems.Thm_ThreeSum_LightArray_linear_bounded_meets_w3sum_ac885d1
-- name    : ThreeSum.LightArray.linear_bounded_meets_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:08:16.118191+00:00
-- url     : https://prove2.me/theorems/02660785-e39b-48f0-a0d2-e157b732d73d
-- title:
--   Light Array: linear bounded meets
-- statement:
--   A convenient polynomial-word bound for both addition and subtraction.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightArray.lean#L65-L86
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightArray.lean#L65-L86

import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Copy
import Definitions.Def_Submission_ThreeSumApsp_Lang_Tactics
import Definitions.Def_Submission_ThreeSum_LightArray
set_option autoImplicit false
open ThreeSum ThreeSum.LightArray
open Light
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightArray.linear_bounded_meets_w3sum_ac885d1 {p : ℕ} (hp : P[p]? = some linearBody)
    {μ : ℕ → ℤ} {srcA srcB dst n U : ℕ} {c : ℤ}
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hA : srcA + n ≤ lim.space) (hB : srcB + n ≤ lim.space)
    (hD : dst + n ≤ lim.space)
    (hsepA : SourceSafe srcA dst n) (hsepB : SourceSafe srcB dst n)
    (hc : |c| ≤ 1) (hword : 2 * (U : ℤ) ≤ lim.word)
    (hvalues : ∀ i < n, |μ (srcA + i)| ≤ U ∧ |μ (srcB + i)| ≤ U) :
    Meets lim P p d [(srcA : ℤ), srcB, dst, n, c] μ (linearTime n) fun _ μ' =>
      (∀ i < n, μ' (dst + i) = μ (srcA + i) + c * μ (srcB + i)) ∧
        SameOutside μ μ' dst n := by sorry
