-- Prove2me | Theorems.Thm_ThreeSum_LightSparseQuery_time_bound
-- name    : ThreeSum.LightSparseQuery.time_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:28:23.336162+00:00
-- url     : https://prove2.me/theorems/bdb42fe7-056f-41d7-bab1-f29a9b915200
-- title:
--   Light Sparse Query: time bound
-- statement:
--   The Light Sparse Query construction uses the time bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSparseQuery.lean#L250-L261
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSparseQuery.lean#L250-L261

import Definitions.Def_Submission_ThreeSum_LightExplicitSum
import Definitions.Def_Submission_ThreeSum_LightCanonicalBoxSum
import Definitions.Def_Submission_ThreeSum_LightSparseQuery
import Definitions.Def_WeightedCache3SUM_Alias_395153661a990775
import Theorems.Thm_ThreeSum_LightBoxSum_time_bound
import Theorems.Thm_ThreeSum_LightCanonicalBoxSum_time_bound
import Theorems.Thm_ThreeSum_LightDownsetAddress_time_bound
import Theorems.Thm_ThreeSum_LightDownsetSize_time_bound
import Theorems.Thm_ThreeSum_LightExplicitSum_time_bound
import Theorems.Thm_ThreeSum_LightLeafSum_time_bound
import Theorems.Thm_ThreeSum_LightMaskMinimum_time_bound
import Theorems.Thm_ThreeSum_LightQueryBox_time_bound
import Theorems.Thm_ThreeSum_LightQueryEnumeration_time_bound
import Theorems.Thm_ThreeSum_LightQueryWeights_time_bound
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
open ThreeSum ThreeSum.LightSparseQuery
open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress
open scoped BigOperators
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightSparseQuery.time_bound {W c t : ℕ} (hc : c ≤ W) (ht : t ≤ c+1) :
    time W c t ≤ 14000*(W+1)^3*(queryItems c t+1) := by sorry
