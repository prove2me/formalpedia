-- Prove2me | Theorems.Thm_ThreeSum_LightSourceStages_time_bound
-- name    : ThreeSum.LightSourceStages.time_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:59:23.923785+00:00
-- url     : https://prove2.me/theorems/49a452c0-6669-4c8a-8ab0-32995bf6f38e
-- title:
--   Light Source Stages: time bound
-- statement:
--   The Light Source Stages construction uses the time bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSourceStages.lean#L186-L194
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSourceStages.lean#L186-L194

import Definitions.Def_Submission_ThreeSum_LightSourceBuild
import Definitions.Def_Submission_ThreeSum_SourceTableLayout
import Definitions.Def_Submission_ThreeSum_LightZetaStages
import Definitions.Def_Submission_ThreeSum_LightSourceStages
import Theorems.Thm_ThreeSum_LightDownsetSize_time_bound
import Theorems.Thm_ThreeSum_LightSourceBuild_time_bound
import Theorems.Thm_ThreeSum_LightSourceGather_time_bound
import Theorems.Thm_ThreeSum_LightSourceHistogram_time_bound
import Theorems.Thm_ThreeSum_LightSourceResidues_time_bound
import Theorems.Thm_ThreeSum_LightSubsetEnumerationSetup_time_bound
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_time_bound
import Theorems.Thm_ThreeSum_LightSubsetSetup_time_bound
import Theorems.Thm_ThreeSum_LightZetaBatch_time_bound
import Theorems.Thm_ThreeSum_LightZetaCell_time_bound
import Definitions.Def_WeightedCache3SUM_Alias_223d9caf4e7f660b
import Definitions.Def_WeightedCache3SUM_Alias_c2a1891cab57c5b2

set_option autoImplicit false
open ThreeSum ThreeSum.LightSourceStages
open Light SubsetAddress LightSubsetAddress LightPascal LightZetaCell
set_option maxHeartbeats 2200000
set_option maxRecDepth 12000
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightSourceStages.time_bound {N L cut p m U D E : ℕ} (hcut : cut ≤ L) :
    time N L cut p m U D E ≤
      278*N*(Nat.log 2 (U+1)+Nat.log 2 (p+D+1)+1)+
      157*downsetCap L cut*(Nat.log 2 (E+1)+1)+13*m+
      6000*(L+1)^4*(downsetCap L cut+1)+269 := by sorry
