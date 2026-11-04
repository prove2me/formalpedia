-- Prove2me | Theorems.Thm_ThreeSum_LightMinimum_least_lt
-- name    : ThreeSum.LightMinimum.least_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:25:35.104557+00:00
-- url     : https://prove2.me/theorems/01d557fa-785c-49ca-9cf9-2519ef9ac819
-- title:
--   Light Minimum: least lt
-- statement:
--   The Light Minimum construction uses the least lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightMinimum.lean#L19-L28
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightMinimum.lean#L19-L28

import Definitions.Def_Submission_ThreeSum_LightArray
import Definitions.Def_Submission_ThreeSum_Balancing
import Definitions.Def_Submission_ThreeSum_LightMinimum
set_option autoImplicit false
open ThreeSum ThreeSum.LightMinimum
open Light

theorem ThreeSum.LightMinimum.least_lt (f : ℕ → ℤ) {n : ℕ} (hn : 0 < n) : least f n < n := by sorry
