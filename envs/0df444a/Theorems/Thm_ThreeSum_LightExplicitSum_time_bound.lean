-- Prove2me | Theorems.Thm_ThreeSum_LightExplicitSum_time_bound
-- name    : ThreeSum.LightExplicitSum.time_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:22:15.406893+00:00
-- url     : https://prove2.me/theorems/3b72a607-d0a6-4780-8d95-54cda1e287b4
-- title:
--   Light Explicit Sum: time bound
-- statement:
--   The Light Explicit Sum construction uses the time bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightExplicitSum.lean#L268-L273
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightExplicitSum.lean#L268-L273

import Definitions.Def_Submission_ThreeSum_ExplicitLayers
import Definitions.Def_Submission_ThreeSum_LightLeafSum
import Definitions.Def_Submission_ThreeSum_LightQueryEnumeration
import Definitions.Def_Submission_ThreeSum_LightExplicitSum
import Definitions.Def_WeightedCache3SUM_Alias_395153661a990775
import Theorems.Thm_ThreeSum_LightDownsetAddress_time_bound
import Theorems.Thm_ThreeSum_LightDownsetSize_time_bound
import Theorems.Thm_ThreeSum_LightLeafSum_time_bound
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
open ThreeSum ThreeSum.LightExplicitSum
open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress
open QueryCoordinates
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightExplicitSum.time_bound {W c t : ℕ} (ht : t ≤ W+1) :
    time W c t ≤ 8200*(W+1)^3*(layerOffset c t+1) := by sorry
