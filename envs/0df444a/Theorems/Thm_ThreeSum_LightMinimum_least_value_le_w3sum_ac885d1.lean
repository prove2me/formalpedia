-- Prove2me | Theorems.Thm_ThreeSum_LightMinimum_least_value_le_w3sum_ac885d1
-- name    : ThreeSum.LightMinimum.least_value_le_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:13:15.620998+00:00
-- url     : https://prove2.me/theorems/40793330-34b1-4e18-bf5b-05198bece048
-- title:
--   Light Minimum: least value le
-- statement:
--   The Light Minimum construction uses the least value le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightMinimum.lean#L36-L51
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightMinimum.lean#L36-L51

import Definitions.Def_Submission_ThreeSum_LightArray
import Definitions.Def_Submission_ThreeSum_Balancing
import Definitions.Def_Submission_ThreeSum_LightMinimum
set_option autoImplicit false
open ThreeSum ThreeSum.LightMinimum
open Light

theorem ThreeSum.LightMinimum.least_value_le_w3sum_ac885d1 (f : ℕ → ℤ) (n i : ℕ) (hi : i < n) :
    f (least f n) ≤ f i := by sorry
