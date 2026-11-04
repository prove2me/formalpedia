-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryWeightedSum_sum_succ
-- name    : ThreeSum.LightTernaryWeightedSum.sum_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:21:28.785479+00:00
-- url     : https://prove2.me/theorems/5e010f94-f024-4d3d-bf0d-c05a481a5a45
-- title:
--   Light Ternary Weighted Sum: sum succ
-- statement:
--   The Light Ternary Weighted Sum construction uses the sum succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryWeightedSum.lean#L15-L17
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryWeightedSum.lean#L15-L17

import Definitions.Def_Submission_ThreeSum_LightLookupSum
import Definitions.Def_Submission_ThreeSum_LightTernaryWeightedSum
set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryWeightedSum
open Light Finset

theorem ThreeSum.LightTernaryWeightedSum.sum_succ (weights keys : ℕ → ℕ) (f : ℕ → ℤ) (j : ℕ) :
    sum weights keys f (j+1) = sum weights keys f j + (weights j : ℤ)*f (keys j) := by sorry
