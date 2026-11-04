-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryWeightedSum_sum_abs_le
-- name    : ThreeSum.LightTernaryWeightedSum.sum_abs_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:38:14.786108+00:00
-- url     : https://prove2.me/theorems/2608f6f8-f63d-4893-8ea0-187a3c30a0a7
-- title:
--   Light Ternary Weighted Sum: sum abs le
-- statement:
--   The Light Ternary Weighted Sum construction uses the sum abs le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryWeightedSum.lean#L19-L33
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryWeightedSum.lean#L19-L33

import Definitions.Def_Submission_ThreeSum_LightLookupSum
import Definitions.Def_Submission_ThreeSum_LightTernaryWeightedSum
set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryWeightedSum
open Light Finset

theorem ThreeSum.LightTernaryWeightedSum.sum_abs_le (weights keys : ℕ → ℕ) (f : ℕ → ℤ) {n j U : ℕ}
    (hw : ∀ i < n, weights i ≤ 2) (hf : ∀ i < n, |f (keys i)| ≤ U)
    (hj : j ≤ n) : |sum weights keys f j| ≤ 2*j*(U : ℤ) := by sorry
