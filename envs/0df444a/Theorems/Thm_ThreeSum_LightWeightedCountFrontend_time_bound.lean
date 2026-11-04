-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedCountFrontend_time_bound
-- name    : ThreeSum.LightWeightedCountFrontend.time_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:11:27.316358+00:00
-- url     : https://prove2.me/theorems/157badd9-41c3-4e06-8aed-216fe692ea4f
-- title:
--   Light Weighted Count Frontend: time bound
-- statement:
--   The Light Weighted Count Frontend construction uses the time bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/CountFrontend.lean#L174-L180
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/CountFrontend.lean#L174-L180

import Definitions.Def_Submission_ThreeSum_ReportingHostRelocation
import Definitions.Def_Submission_Weighted_GroupBankResources
import Definitions.Def_Submission_Weighted_WantedRows
import Definitions.Def_Submission_Weighted_CountFrontend
import Theorems.Thm_ThreeSum_LightCacheEnumeration_time_bound
import Theorems.Thm_ThreeSum_LightMaskBits_time_bound
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_time_bound
import Theorems.Thm_ThreeSum_LightTernaryDivide_time_bound
import Theorems.Thm_ThreeSum_LightTernaryEnumeration_time_bound
import Theorems.Thm_ThreeSum_LightTernaryEulerMemo_time_bound
import Theorems.Thm_ThreeSum_LightTernaryEulerRow_time_bound
import Theorems.Thm_ThreeSum_LightTernaryInversePass_time_bound
import Theorems.Thm_ThreeSum_LightTernaryLookup_time_bound
import Theorems.Thm_ThreeSum_LightTernaryMetadata_time_bound
import Theorems.Thm_ThreeSum_LightTernaryPass_time_bound
import Theorems.Thm_ThreeSum_LightTernaryQueryLookup_time_bound
import Theorems.Thm_ThreeSum_LightTernaryRankTable_time_bound
import Theorems.Thm_ThreeSum_LightWeightedBankAssembly_time_bound
import Theorems.Thm_ThreeSum_LightWeightedBankCoordinate_time_bound
import Theorems.Thm_ThreeSum_LightWeightedBankSweep_time_bound
import Theorems.Thm_ThreeSum_LightWeightedEulerMetadata_time_bound
import Theorems.Thm_ThreeSum_LightWeightedGroupBankStep_time_bound
import Theorems.Thm_ThreeSum_LightWeightedGroupedBanks_time_bound
import Theorems.Thm_ThreeSum_LightWeightedNearEnumeration_time_bound
import Theorems.Thm_ThreeSum_LightWeightedNearSetup_time_bound
import Theorems.Thm_ThreeSum_LightWeightedNearSource_time_bound
import Theorems.Thm_ThreeSum_LightWeightedPredecessorTable_time_bound
import Theorems.Thm_ThreeSum_LightWeightedPredecessor_time_bound

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightWeightedCountFrontend
open Light ThreeSum.LightSubsetAddress ThreeSum.TernaryJointType ThreeSum.TernaryBank
open ThreeSum.WeightedBankEnumeration (cacheCost)
open ThreeSum.TernaryCodeSemantics ThreeSum.TernaryFrozenQueryStages ThreeSum.WeightedBankStageModel
open ThreeSum.LightWeightedNearPair ThreeSum.LightWeightedWantedRowDispatch ThreeSum.LightWeightedPreparedState
set_option maxHeartbeats 8000000
set_option maxRecDepth 18000

theorem ThreeSum.LightWeightedCountFrontend.time_bound (groups N L n count t : ℕ) :
    time groups N L n count t≤40000*(groups+1)*(N+1)*(N+L+1)*(n+1)+(count+1)*(t+1000) := by sorry
