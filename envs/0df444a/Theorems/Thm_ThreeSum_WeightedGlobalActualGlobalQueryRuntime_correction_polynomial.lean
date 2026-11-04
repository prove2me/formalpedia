-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalActualGlobalQueryRuntime_correction_polynomial
-- name    : ThreeSum.WeightedGlobalActualGlobalQueryRuntime.correction_polynomial
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T23:59:31.692245+00:00
-- url     : https://prove2.me/theorems/1ea2aa99-0ad8-49fb-8ad2-93a5a607408e
-- title:
--   Weighted Global Actual Global Query Runtime: correction polynomial
-- statement:
--   The Weighted Global Actual Global Query Runtime construction uses the correction polynomial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryActualGlobalQueryRuntime.lean#L295-L313
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryActualGlobalQueryRuntime.lean#L295-L313

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryActualColoredRuntime
import Definitions.Def_Submission_Weighted_Global_TernaryUniformQueryTime
import Definitions.Def_Submission_Weighted_Global_TernaryActualGlobalQueryRuntime
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalActualGlobalQueryRuntime
open Light Real Filter StageBounds
open TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps
open WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate WeightedGlobalNativeCompleteFrontend
open WeightedGlobalActualPrefixRuntime WeightedGlobalActualSeedRuntime WeightedGlobalActualColoredRuntime
open WeightedGlobalOversizePrime WeightedGlobalOversizeRates WeightedGlobalOversizeOverhead WeightedGlobalCoverScale WeightedGlobalEntropyRates
open scoped Topology BigOperators
set_option maxHeartbeats 6000000
set_option maxRecDepth 24000
attribute [local instance] Classical.propDecidable

theorem ThreeSum.WeightedGlobalActualGlobalQueryRuntime.correction_polynomial {K k m F n Hdet : ℕ} (S : State K m)
    (hJ : radixLength m n≤S.arena.J) :
    totalCorrection k F Hdet S n≤
      (16*menuCoefficient K (nativePrime K m)+(TernaryMomentSchedule.channels (2*Hdet+1)).length)*
        (S.arena.J+1)^7*(wantedCap K k m F n S.arena.J*queryCap S n):= by sorry
