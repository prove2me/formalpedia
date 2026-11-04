-- Prove2me | Theorems.Thm_ThreeSum_LightReportingSuffixExplicit_time_bound
-- name    : ThreeSum.LightReportingSuffixExplicit.time_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:04:23.529855+00:00
-- url     : https://prove2.me/theorems/16dc0989-dbbe-4a47-8d75-1527e03c1991
-- title:
--   Light Reporting Suffix Explicit: time bound
-- statement:
--   The Light Reporting Suffix Explicit construction uses the time bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightReportingSuffixExplicit.lean#L177-L182
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightReportingSuffixExplicit.lean#L177-L182

import Definitions.Def_Submission_ThreeSum_LightReportingSuffixSum
import Definitions.Def_Submission_ThreeSum_LightExplicitSum
import Definitions.Def_Submission_ThreeSum_LightReportingSuffixExplicit
import Definitions.Def_WeightedCache3SUM_Alias_395153661a990775
import Theorems.Thm_ThreeSum_LightBoxSum_time_bound
import Theorems.Thm_ThreeSum_LightCanonicalBoxSum_time_bound
import Theorems.Thm_ThreeSum_LightDownsetAddress_time_bound
import Theorems.Thm_ThreeSum_LightDownsetSize_time_bound
import Theorems.Thm_ThreeSum_LightExplicitSum_time_bound
import Theorems.Thm_ThreeSum_LightLeafSum_time_bound
import Theorems.Thm_ThreeSum_LightMaskMinimum_time_bound
import Theorems.Thm_ThreeSum_LightMaskUnion_time_bound
import Theorems.Thm_ThreeSum_LightQueryBox_time_bound
import Theorems.Thm_ThreeSum_LightQueryEnumeration_time_bound
import Theorems.Thm_ThreeSum_LightQueryWeights_time_bound
import Theorems.Thm_ThreeSum_LightReportingSuffixCell_time_bound
import Theorems.Thm_ThreeSum_LightReportingSuffixSum_time_bound
import Theorems.Thm_ThreeSum_LightSignedBoxSetup_time_bound
import Theorems.Thm_ThreeSum_LightSignedLeafBatch_time_bound
import Theorems.Thm_ThreeSum_LightSignedLeafCell_time_bound
import Theorems.Thm_ThreeSum_LightSignedLeafGeneral_time_bound
import Theorems.Thm_ThreeSum_LightSignedLeafTable_time_bound
import Theorems.Thm_ThreeSum_LightSignedLeaf_time_bound
import Theorems.Thm_ThreeSum_LightSparseQuery_time_bound
import Theorems.Thm_ThreeSum_LightStageLookup_time_bound
import Theorems.Thm_ThreeSum_LightSubsetEnumerationSetup_time_bound
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_time_bound
import Theorems.Thm_ThreeSum_LightSubsetSetup_time_bound
import Theorems.Thm_ThreeSum_LightZetaBatch_time_bound
import Theorems.Thm_ThreeSum_LightZetaCell_time_bound
import Definitions.Def_WeightedCache3SUM_Alias_223d9caf4e7f660b
import Definitions.Def_WeightedCache3SUM_Alias_c2a1891cab57c5b2

set_option autoImplicit false
open ThreeSum ThreeSum.LightReportingSuffixExplicit
open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress
open QueryCoordinates ReportingHostSuffix
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightReportingSuffixExplicit.time_bound {W c t : ℕ} (ht : t ≤ W+1) :
    time W c t ≤ 11000*(W+1)^3*(layerOffset c t+1) := by sorry
