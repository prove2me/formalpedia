-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryWeightedHistogram_total_abs_le
-- name    : ThreeSum.LightTernaryWeightedHistogram.total_abs_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:55:57.343563+00:00
-- url     : https://prove2.me/theorems/1cc7f13c-1cda-4505-8f0c-971455a51959
-- title:
--   Light Ternary Weighted Histogram: total abs le
-- statement:
--   The Light Ternary Weighted Histogram construction uses the total abs le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryWeightedHistogram.lean#L30-L41
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryWeightedHistogram.lean#L30-L41

import Definitions.Def_Submission_ThreeSum_LightHistogram
import Definitions.Def_Submission_ThreeSum_LightTernaryWeightedHistogram
set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryWeightedHistogram
open Light Finset
open scoped BigOperators
set_option maxHeartbeats 2000000

theorem ThreeSum.LightTernaryWeightedHistogram.total_abs_le (key : ℕ → ℕ) (weight : ℕ → ℤ) (r n U : ℕ)
    (h : ∀ i < n, |weight i| ≤ U) : |total key weight r n| ≤ (n : ℤ)*U := by sorry
