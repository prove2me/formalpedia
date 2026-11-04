-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryWeightedHistogram_time_bound
-- name    : ThreeSum.LightTernaryWeightedHistogram.time_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:27:56.902199+00:00
-- url     : https://prove2.me/theorems/0c10fa6b-84cf-404b-ab89-093624916287
-- title:
--   Light Ternary Weighted Histogram: time bound
-- statement:
--   The Light Ternary Weighted Histogram construction uses the time bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryWeightedHistogram.lean#L178-L180
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryWeightedHistogram.lean#L178-L180

import Definitions.Def_Submission_ThreeSum_LightHistogram
import Definitions.Def_Submission_ThreeSum_LightTernaryWeightedHistogram
set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryWeightedHistogram
open Light Finset
open scoped BigOperators
set_option maxHeartbeats 2000000
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightTernaryWeightedHistogram.time_bound (n bank : ℕ) : time n bank ≤ 100*(n+bank+1) := by sorry
