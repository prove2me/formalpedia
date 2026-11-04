-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryWeightedHistogram_total_succ
-- name    : ThreeSum.LightTernaryWeightedHistogram.total_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:18:27.663213+00:00
-- url     : https://prove2.me/theorems/1a25f1e3-d2fd-4824-8144-e1d68151554b
-- title:
--   Light Ternary Weighted Histogram: total succ
-- statement:
--   The Light Ternary Weighted Histogram construction uses the total succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryWeightedHistogram.lean#L24-L28
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryWeightedHistogram.lean#L24-L28

import Definitions.Def_Submission_ThreeSum_LightHistogram
import Definitions.Def_Submission_ThreeSum_LightTernaryWeightedHistogram
set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryWeightedHistogram
open Light Finset
open scoped BigOperators
set_option maxHeartbeats 2000000

theorem ThreeSum.LightTernaryWeightedHistogram.total_succ (key : ℕ → ℕ) (weight : ℕ → ℤ) (r n : ℕ) :
    total key weight r (n+1)=total key weight r n+
      if key n=r then weight n else 0 := by sorry
