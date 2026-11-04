-- Prove2me | Theorems.Thm_ThreeSum_LightTernarySourceHistogram_time_bound
-- name    : ThreeSum.LightTernarySourceHistogram.time_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:45:05.814055+00:00
-- url     : https://prove2.me/theorems/ce239079-bb9d-4f36-9655-76c62a03098a
-- title:
--   Light Ternary Source Histogram: time bound
-- statement:
--   The Light Ternary Source Histogram construction uses the time bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernarySourceHistogram.lean#L115-L119
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernarySourceHistogram.lean#L115-L119

import Definitions.Def_Submission_ThreeSum_LightTernarySourceKeys
import Definitions.Def_Submission_ThreeSum_LightTernarySourceHistogram
import Theorems.Thm_ThreeSum_LightTernaryLookup_time_bound
import Theorems.Thm_ThreeSum_LightTernarySourceKeys_time_bound

set_option autoImplicit false
open ThreeSum ThreeSum.LightTernarySourceHistogram
open Light ThreeSum.LightArray ThreeSum.LightSubsetAddress
set_option maxHeartbeats 2000000
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightTernarySourceHistogram.time_bound (L count bank : ℕ) :
    time L count bank ≤ 1000*(L+1)*(count+bank+1) := by sorry
