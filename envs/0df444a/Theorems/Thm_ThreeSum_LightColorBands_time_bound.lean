-- Prove2me | Theorems.Thm_ThreeSum_LightColorBands_time_bound
-- name    : ThreeSum.LightColorBands.time_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:39:40.460203+00:00
-- url     : https://prove2.me/theorems/769733cd-05d4-4095-81b0-d3e5b036fef0
-- title:
--   Light Color Bands: time bound
-- statement:
--   The Light Color Bands construction uses the time bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightColorBands.lean#L169-L173
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightColorBands.lean#L169-L173

import Definitions.Def_Submission_ThreeSum_LightColorClasses
import Definitions.Def_Submission_ThreeSum_ColorBandBounds
import Definitions.Def_Submission_ThreeSum_LightColorBands
import Theorems.Thm_ThreeSum_LightBandEnumeration_time_bound
import Theorems.Thm_ThreeSum_LightBandPartition_time_bound
import Definitions.Def_WeightedCache3SUM_Alias_2186ec26acc49293
import Theorems.Thm_ThreeSum_LightColorArray_time_bound
import Theorems.Thm_ThreeSum_LightColorClasses_time_bound
import Theorems.Thm_ThreeSum_LightColorIndex_time_bound
import Theorems.Thm_ThreeSum_LightKaratsuba_time_bound
import Theorems.Thm_ThreeSum_LightNormalize_time_bound
import Theorems.Thm_ThreeSum_LightSmallDivide_time_bound
import Theorems.Thm_ThreeSum_LightSortedBands_time_bound

set_option autoImplicit false
open ThreeSum ThreeSum.LightColorBands
open Light ColorClassLists
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightColorBands.time_bound (W n g : ℕ) :
    time W n g ≤ 1200*(W+1)*(n+1)+ColorBandBounds.time n g+300 := by sorry
