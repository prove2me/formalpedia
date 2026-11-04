-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryWeightedSum_sum_zero
-- name    : ThreeSum.LightTernaryWeightedSum.sum_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:28:13.986401+00:00
-- url     : https://prove2.me/theorems/f59edc4f-7fe6-44fc-b1e4-ba56a6f30b19
-- title:
--   Light Ternary Weighted Sum: sum zero
-- statement:
--   The Light Ternary Weighted Sum construction uses the sum zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryWeightedSum.lean#L12-L13
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryWeightedSum.lean#L12-L13

import Definitions.Def_Submission_ThreeSum_LightLookupSum
import Definitions.Def_Submission_ThreeSum_LightTernaryWeightedSum
set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryWeightedSum
open Light Finset

theorem ThreeSum.LightTernaryWeightedSum.sum_zero (weights keys : ℕ → ℕ) (f : ℕ → ℤ) : sum weights keys f 0 = 0 := by sorry
