-- Prove2me | Theorems.Thm_ThreeSum_LightSourceRetainedStages_time_bound
-- name    : ThreeSum.LightSourceRetainedStages.time_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:08:51.178323+00:00
-- url     : https://prove2.me/theorems/24e287a6-a248-4b29-8d04-15a389af7ab8
-- title:
--   Light Source Retained Stages: time bound
-- statement:
--   The Light Source Retained Stages construction uses the time bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSourceRetainedStages.lean#L138-L144
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSourceRetainedStages.lean#L138-L144

import Definitions.Def_Submission_ThreeSum_LightSourceStages
import Definitions.Def_Submission_ThreeSum_LightSourceRetainedStages
import Theorems.Thm_ThreeSum_LightDownsetSize_time_bound
import Theorems.Thm_ThreeSum_LightSourceBuild_time_bound
import Theorems.Thm_ThreeSum_LightSourceGather_time_bound
import Theorems.Thm_ThreeSum_LightSourceHistogram_time_bound
import Theorems.Thm_ThreeSum_LightSourceResidues_time_bound
import Theorems.Thm_ThreeSum_LightSourceStages_time_bound
import Theorems.Thm_ThreeSum_LightSubsetEnumerationSetup_time_bound
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_time_bound
import Theorems.Thm_ThreeSum_LightSubsetSetup_time_bound
import Theorems.Thm_ThreeSum_LightZetaBatch_time_bound
import Theorems.Thm_ThreeSum_LightZetaCell_time_bound
import Definitions.Def_WeightedCache3SUM_Alias_223d9caf4e7f660b
import Definitions.Def_WeightedCache3SUM_Alias_c2a1891cab57c5b2

set_option autoImplicit false
open ThreeSum ThreeSum.LightSourceRetainedStages
open Light SubsetAddress LightSubsetAddress LightPascal LightZetaCell
set_option maxHeartbeats 1800000
set_option maxRecDepth 12000
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightSourceRetainedStages.time_bound {L cut E : ℕ} (hcut : cut ≤ L) :
    time L cut E ≤ 157*downsetCap L cut*(Nat.log 2 (E+1)+1)+
      6000*(L+1)^4*(downsetCap L cut+1)+106 := by sorry
