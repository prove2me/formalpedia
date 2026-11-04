-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaLoop_Ready_start
-- name    : ThreeSum.WeightedGlobalArenaLoop.Ready.start
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T02:18:12.231264+00:00
-- url     : https://prove2.me/theorems/64713ddd-733c-4f39-b5c9-b3245945659f
-- title:
--   Ready: start
-- statement:
--   The Ready construction uses the start property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaLoop.lean#L195-L216
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaLoop.lean#L195-L216

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaLoopState
import Definitions.Def_Submission_Weighted_Global_TernaryArenaLoop
import Theorems.Thm_ThreeSum_WeightedGlobalArenaFrontBounds_capacity
import Theorems.Thm_ThreeSum_WeightedGlobalArenaPrefixState_start
import Theorems.Thm_ThreeSum_WeightedGlobalArenaScoreScan_initial

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaLoop
open Light TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps WeightedGlobalArenaLayout
open WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate WeightedGlobalArenaSeedData
open WeightedGlobalArenaSelectedBudgets WeightedGlobalArenaAllocation WeightedGlobalArenaPrefixInputs
open LightWeightedGlobalSeedScoreFactory LightWeightedGlobalControllerFactory
set_option maxHeartbeats 6000000
set_option maxRecDepth 24000
variable {p m F K N : ℕ} [Fact p.Prime]
variable {E : Type*} [Field E] [Fintype E] [DecidableEq E] [Algebra (ZMod p) E]

theorem ThreeSum.WeightedGlobalArenaLoop.Ready.start {S : Setup p m F K N E} {lim : Limits} {depth : ℕ}
    (H : Ready S lim depth) {μ ν : ℕ→ℤ}
    (hinit : LightWeightedGlobalPrefixInit.Initialized (config p 0 S.input S.arrays 0)
      (addr S.input.free S.input.capacity 3) (S.seedHeader 0) μ ν)
    (hkeep : Kept S.initial μ S.input.free)
    (hTemplate : Seg μ (addr S.input.free S.input.capacity 0)
      (WeightedGlobalArenaHeaderAgreement.templateValues S.input p m F)) : Invariant S 0 ν := by sorry
