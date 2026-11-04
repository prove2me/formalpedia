-- Prove2me | Theorems.Thm_ThreeSum_LightSignedLeafGeneral_time_bound
-- name    : ThreeSum.LightSignedLeafGeneral.time_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:16:08.731753+00:00
-- url     : https://prove2.me/theorems/6ba6f012-edd4-41b1-892b-2dcbac42508f
-- title:
--   Light Signed Leaf General: time bound
-- statement:
--   The Light Signed Leaf General construction uses the time bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSignedLeafGeneral.lean#L168-L172
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSignedLeafGeneral.lean#L168-L172

import Definitions.Def_Submission_ThreeSum_LightSignedLeaf
import Definitions.Def_Submission_ThreeSum_LightMaskUnion
import Definitions.Def_Submission_ThreeSum_LightSignedLeafGeneral
import Definitions.Def_WeightedCache3SUM_Alias_395153661a990775
import Theorems.Thm_ThreeSum_LightDownsetAddress_time_bound
import Theorems.Thm_ThreeSum_LightDownsetSize_time_bound
import Theorems.Thm_ThreeSum_LightMaskUnion_time_bound
import Theorems.Thm_ThreeSum_LightSignedLeaf_time_bound
import Theorems.Thm_ThreeSum_LightStageLookup_time_bound
import Theorems.Thm_ThreeSum_LightSubsetEnumerationSetup_time_bound
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_time_bound
import Theorems.Thm_ThreeSum_LightSubsetSetup_time_bound
import Theorems.Thm_ThreeSum_LightZetaBatch_time_bound
import Theorems.Thm_ThreeSum_LightZetaCell_time_bound
import Definitions.Def_WeightedCache3SUM_Alias_223d9caf4e7f660b
import Definitions.Def_WeightedCache3SUM_Alias_c2a1891cab57c5b2

set_option autoImplicit false
open ThreeSum ThreeSum.LightSignedLeafGeneral
open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightSignedLeafGeneral.time_bound (W : ℕ) : time W ≤ 7800*(W+1)^2 := by sorry
