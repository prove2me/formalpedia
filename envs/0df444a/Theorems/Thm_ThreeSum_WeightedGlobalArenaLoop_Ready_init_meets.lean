-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaLoop_Ready_init_meets
-- name    : ThreeSum.WeightedGlobalArenaLoop.Ready.init_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T02:18:38.46474+00:00
-- url     : https://prove2.me/theorems/5a3e8ccf-2789-4dc7-9993-25184754ed73
-- title:
--   Ready: init meets
-- statement:
--   The entire actual 197-procedure prefix program, including zero
--   initialization, executes from real constructed control headers.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaLoop.lean#L220-L249
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaLoop.lean#L220-L249

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaLoopState
import Definitions.Def_Submission_Weighted_Global_TernaryArenaLoop
import Theorems.Thm_ThreeSum_WeightedGlobalArenaFrontBounds_capacity
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

theorem ThreeSum.WeightedGlobalArenaLoop.Ready.init_meets {S : Setup p m F K N E} {lim : Limits} {depth : ℕ}
    (H : Ready S lim (depth+1)) (μ : ℕ→ℤ)
    (hkeep : Kept S.initial μ S.input.free)
    (hTemplate : Seg μ (addr S.input.free S.input.capacity 0)
      (WeightedGlobalArenaHeaderAgreement.templateValues S.input p m F))
    (hSeed : Seg μ (addr S.input.free S.input.capacity 2) (S.seedHeader 0)) :
    Meets lim S.program 194 depth S.initArgs μ S.initTime
      (fun z ν=>z=((p^S.rounds:ℕ):ℤ) ∧ Invariant S S.rounds ν) := by sorry
