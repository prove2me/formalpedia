-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaPhaseFrames_input_lt_mask
-- name    : ThreeSum.WeightedGlobalArenaPhaseFrames.input_lt_mask
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T01:03:45.612515+00:00
-- url     : https://prove2.me/theorems/7f3bc80e-24d6-4806-8345-612e41ddbdaf
-- title:
--   Weighted Global Arena Phase Frames: input lt mask
-- statement:
--   The original input-length sentinel fits the canonical 2N-bit mask.
--   This uses the true input length, even when deduplication shrinks the arrays.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaPhaseFrames.lean#L151-L160
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaPhaseFrames.lean#L151-L160

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPhase
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPhaseFrames
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaPhaseFrames
open Light WeightedGlobalArenaLayout WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate
open LightWeightedGlobalSeedScoreFactory LightWeightedGlobalControllerFactory
open WeightedGlobalArenaControllerPlan WeightedGlobalArenaScoreScan
variable {p m F : ℕ} [Fact p.Prime]
set_option maxHeartbeats 6000000
set_option maxRecDepth 24000
open TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps
open WeightedGlobalArenaSeedData WeightedGlobalArenaPrefixInputs WeightedGlobalNativeCompleteFrontend
open WeightedGlobalArenaSelectedBudgets WeightedGlobalArenaAllocation WeightedGlobalArenaPhase
variable {E : Type*} [Field E] [Fintype E] [DecidableEq E] [Algebra (ZMod p) E]

theorem ThreeSum.WeightedGlobalArenaPhaseFrames.input_lt_mask {n M r L : ℕ} (hn : 1<n) (hsize : n^2≤M^r) (hM : M≤4^L) :
    n<2^(2*(r*L)) := by sorry
