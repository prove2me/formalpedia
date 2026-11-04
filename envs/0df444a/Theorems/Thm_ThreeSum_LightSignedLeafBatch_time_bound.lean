-- Prove2me | Theorems.Thm_ThreeSum_LightSignedLeafBatch_time_bound
-- name    : ThreeSum.LightSignedLeafBatch.time_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:27:25.264933+00:00
-- url     : https://prove2.me/theorems/4cd62eb4-5594-48a4-902e-66d3b25b09c7
-- title:
--   Light Signed Leaf Batch: time bound
-- statement:
--   The Light Signed Leaf Batch construction uses the time bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSignedLeafBatch.lean#L158-L164
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSignedLeafBatch.lean#L158-L164

import Definitions.Def_Submission_ThreeSum_LightSignedLeafCell
import Definitions.Def_Submission_ThreeSum_MaskDecode
import Definitions.Def_Submission_ThreeSum_LightSignedLeafBatch
import Definitions.Def_WeightedCache3SUM_Alias_395153661a990775
import Theorems.Thm_ThreeSum_LightDownsetAddress_time_bound
import Theorems.Thm_ThreeSum_LightDownsetSize_time_bound
import Theorems.Thm_ThreeSum_LightMaskUnion_time_bound
import Theorems.Thm_ThreeSum_LightSignedLeafCell_time_bound
import Theorems.Thm_ThreeSum_LightSignedLeafGeneral_time_bound
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
open ThreeSum ThreeSum.LightSignedLeafBatch
open Light ThreeSum.SubsetAddress ThreeSum.LightZetaCell ThreeSum.MaskDecode
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightSignedLeafBatch.time_bound (W n : ℕ) : time W n ≤ 9400*(W+1)^2*(n+1) := by sorry
