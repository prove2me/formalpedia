-- Prove2me | Theorems.Thm_ThreeSum_LightBandRawAColor_time_bound
-- name    : ThreeSum.LightBandRawAColor.time_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:48:24.983282+00:00
-- url     : https://prove2.me/theorems/07365f10-0f81-4ba4-93fd-f5a281cffde3
-- title:
--   Light Band Raw AColor: time bound
-- statement:
--   The Light Band Raw AColor construction uses the time bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBandRawAColor.lean#L241-L245
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBandRawAColor.lean#L241-L245

import Definitions.Def_Submission_ThreeSum_LightColorBands
import Definitions.Def_Submission_ThreeSum_LightBandRawACatalog
import Definitions.Def_Submission_ThreeSum_BandRawAOriginal
import Definitions.Def_Submission_ThreeSum_LightBandRawAColor
import Theorems.Thm_ThreeSum_LightBandCandidates_time_bound
import Theorems.Thm_ThreeSum_LightBandEnumeration_time_bound
import Theorems.Thm_ThreeSum_LightBandPartition_time_bound
import Definitions.Def_WeightedCache3SUM_Alias_2186ec26acc49293
import Theorems.Thm_ThreeSum_LightBandRawACatalog_time_bound
import Theorems.Thm_ThreeSum_LightBandRawA_time_bound
import Theorems.Thm_ThreeSum_LightBlockCoefficients_time_bound
import Theorems.Thm_ThreeSum_LightColorArray_time_bound
import Theorems.Thm_ThreeSum_LightColorBands_time_bound
import Theorems.Thm_ThreeSum_LightColorClasses_time_bound
import Theorems.Thm_ThreeSum_LightColorIndex_time_bound
import Theorems.Thm_ThreeSum_LightKaratsuba_time_bound
import Theorems.Thm_ThreeSum_LightLocalKeyRow_time_bound
import Theorems.Thm_ThreeSum_LightLocalKeys_time_bound
import Theorems.Thm_ThreeSum_LightMaskBits_time_bound
import Theorems.Thm_ThreeSum_LightMaskHashes_time_bound
import Theorems.Thm_ThreeSum_LightNormalize_time_bound
import Theorems.Thm_ThreeSum_LightResidueHistogram_time_bound
import Theorems.Thm_ThreeSum_LightSmallDivide_time_bound
import Theorems.Thm_ThreeSum_LightSortedBands_time_bound

set_option autoImplicit false
open ThreeSum ThreeSum.LightBandRawAColor
open Light BandPartition BandCandidateRows BandRawA ColorClassLists
set_option maxHeartbeats 2400000
set_option maxRecDepth 11000
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightBandRawAColor.time_bound (W n g : ℕ) :
    time W n g ≤ 1200*(W+1)*(n+1)+ColorBandBounds.time n g+catalogTime n g+600 := by sorry
