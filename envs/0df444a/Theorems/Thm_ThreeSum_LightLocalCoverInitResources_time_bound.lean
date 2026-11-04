-- Prove2me | Theorems.Thm_ThreeSum_LightLocalCoverInitResources_time_bound
-- name    : ThreeSum.LightLocalCoverInitResources.time_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:50:49.472346+00:00
-- url     : https://prove2.me/theorems/ebd786ab-c32e-4d24-b174-ee52a39560d5
-- title:
--   Light Local Cover Init Resources: time bound
-- statement:
--   The Light Local Cover Init Resources construction uses the time bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightLocalCoverInitResources.lean#L39-L47
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightLocalCoverInitResources.lean#L39-L47

import Definitions.Def_Submission_ThreeSum_LightLocalCoverInit
import Definitions.Def_Submission_ThreeSum_LightLocalCoverResources
import Definitions.Def_Submission_ThreeSum_LightLocalCoverInitResources
import Theorems.Thm_ThreeSum_LightBlockCoefficients_time_bound
import Theorems.Thm_ThreeSum_LightLocalCounts_time_bound
import Theorems.Thm_ThreeSum_LightLocalCoverResources_time_bound
import Theorems.Thm_ThreeSum_LightLocalCoverRow_time_bound
import Theorems.Thm_ThreeSum_LightMaskBits_time_bound
import Theorems.Thm_ThreeSum_LightMaskHashes_time_bound
import Theorems.Thm_ThreeSum_LightPairFlags_time_bound
import Theorems.Thm_ThreeSum_LightResidueHistogram_time_bound
import Definitions.Def_WeightedCache3SUM_Alias_ea9db4f154655ba6
import Theorems.Thm_ThreeSum_LightSmallDivide_time_bound
import Theorems.Thm_ThreeSum_LightSubsetEnumerationSetup_time_bound
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_time_bound
import Theorems.Thm_ThreeSum_LightSubsetSetup_time_bound
import Theorems.Thm_ThreeSum_LightWeightDecode_time_bound
import Theorems.Thm_ThreeSum_LightWeightGather_time_bound
import Definitions.Def_WeightedCache3SUM_Alias_e3ac3137889c3add

set_option autoImplicit false
open ThreeSum ThreeSum.LightLocalCoverInitResources
open Light LocalCoverBounds GlobalEncoding LightLocalCoverSchedule LightLocalCoverTables
open LightLocalCoverLayout
set_option maxHeartbeats 1500000

theorem ThreeSum.LightLocalCoverInitResources.time_bound (h : ℕ) : LightLocalCoverInit.time h ≤ envelope h := by sorry
