-- Prove2me | Theorems.Thm_ThreeSum_LightQueryWeights_time_bound
-- name    : ThreeSum.LightQueryWeights.time_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:50:49.865709+00:00
-- url     : https://prove2.me/theorems/236d5ad3-03ef-4cd9-ab51-51b146418073
-- title:
--   Light Query Weights: time bound
-- statement:
--   The Light Query Weights construction uses the time bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightQueryWeights.lean#L169-L171
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightQueryWeights.lean#L169-L171

import Definitions.Def_Submission_ThreeSum_QueryCoordinates
import Definitions.Def_Submission_ThreeSum_LightMaskErase
import Definitions.Def_Submission_ThreeSum_LightQueryWeights
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_time_bound

set_option autoImplicit false
open ThreeSum ThreeSum.LightQueryWeights
open Light ThreeSum.SubsetAddress ThreeSum.MaskErase ThreeSum.LightSubsetAddress
open QueryCoordinates
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightQueryWeights.time_bound (W : ℕ) : time W ≤ 500*(W+1)^2 := by sorry
