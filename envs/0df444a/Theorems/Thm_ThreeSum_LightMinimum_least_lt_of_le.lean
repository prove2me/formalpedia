-- Prove2me | Theorems.Thm_ThreeSum_LightMinimum_least_lt_of_le
-- name    : ThreeSum.LightMinimum.least_lt_of_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:26:50.898452+00:00
-- url     : https://prove2.me/theorems/bb672808-635a-4403-b599-80b147fffc6c
-- title:
--   Light Minimum: least lt of le
-- statement:
--   The Light Minimum construction uses the least lt of le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightMinimum.lean#L30-L34
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightMinimum.lean#L30-L34

import Definitions.Def_Submission_ThreeSum_LightArray
import Definitions.Def_Submission_ThreeSum_Balancing
import Definitions.Def_Submission_ThreeSum_LightMinimum
set_option autoImplicit false
open ThreeSum ThreeSum.LightMinimum
open Light

theorem ThreeSum.LightMinimum.least_lt_of_le (f : ℕ → ℤ) {j n : ℕ} (hn : 0 < n) (hj : j ≤ n) :
    least f j < n := by sorry
