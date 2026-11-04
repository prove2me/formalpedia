-- Prove2me | Theorems.Thm_ThreeSum_LightSignedLeaf_time_bound
-- name    : ThreeSum.LightSignedLeaf.time_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:07:22.078967+00:00
-- url     : https://prove2.me/theorems/9a51561b-7fd3-4785-8b95-34e3346466ae
-- title:
--   Light Signed Leaf: time bound
-- statement:
--   The Light Signed Leaf construction uses the time bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSignedLeaf.lean#L142-L145
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSignedLeaf.lean#L142-L145

import Definitions.Def_Submission_ThreeSum_SignedLeaf
import Definitions.Def_Submission_ThreeSum_LightStageLookup
import Definitions.Def_Submission_ThreeSum_LightSign
import Definitions.Def_Submission_ThreeSum_LightSignedLeaf
import Definitions.Def_WeightedCache3SUM_Alias_395153661a990775
import Theorems.Thm_ThreeSum_LightDownsetAddress_time_bound
import Theorems.Thm_ThreeSum_LightDownsetSize_time_bound
import Theorems.Thm_ThreeSum_LightStageLookup_time_bound
import Theorems.Thm_ThreeSum_LightSubsetEnumerationSetup_time_bound
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_time_bound
import Theorems.Thm_ThreeSum_LightSubsetSetup_time_bound
import Theorems.Thm_ThreeSum_LightZetaBatch_time_bound
import Theorems.Thm_ThreeSum_LightZetaCell_time_bound
import Definitions.Def_WeightedCache3SUM_Alias_223d9caf4e7f660b
import Definitions.Def_WeightedCache3SUM_Alias_c2a1891cab57c5b2

set_option autoImplicit false
open ThreeSum ThreeSum.LightSignedLeaf
open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightSignedLeaf.time_bound (W : ℕ) : time W ≤ 5800*(W+1)^2 := by sorry
