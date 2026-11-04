-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryGroupedSources_time_bound
-- name    : ThreeSum.LightTernaryGroupedSources.time_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:51:48.029704+00:00
-- url     : https://prove2.me/theorems/2e337653-8835-4e8e-a0cf-511da6240187
-- title:
--   Light Ternary Grouped Sources: time bound
-- statement:
--   The Light Ternary Grouped Sources construction uses the time bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryGroupedSources.lean#L113-L118
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryGroupedSources.lean#L113-L118

import Definitions.Def_Submission_ThreeSum_LightTernarySourceHistogram
import Definitions.Def_Submission_ThreeSum_LightTernaryGroupedSourceKeys
import Definitions.Def_Submission_ThreeSum_TernaryWeightedPhysicalSources
import Definitions.Def_Submission_ThreeSum_LightTernaryGroupedSources
import Theorems.Thm_ThreeSum_LightTernaryGroupedSourceKeys_time_bound
import Theorems.Thm_ThreeSum_LightTernaryLookup_time_bound
import Theorems.Thm_ThreeSum_LightTernarySourceHistogram_time_bound
import Theorems.Thm_ThreeSum_LightTernarySourceKeys_time_bound
import Theorems.Thm_ThreeSum_LightTernaryWeightedHistogram_time_bound

set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryGroupedSources
open Light ThreeSum.LightSubsetAddress
set_option maxHeartbeats 3000000
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightTernaryGroupedSources.time_bound (L count bank groups : ℕ) :
    time L count bank groups≤1000*(L+1)*(count+groups*bank+1) := by sorry
