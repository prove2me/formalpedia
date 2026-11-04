-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaInitialSeedHeader_initialized
-- name    : ThreeSum.WeightedGlobalArenaInitialSeedHeader.initialized
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T23:15:30.036224+00:00
-- url     : https://prove2.me/theorems/3cb75f5a-71b4-4372-923d-bc4ad2b1c9dc
-- title:
--   Weighted Global Arena Initial Seed Header: initialized
-- statement:
--   The real budget initialization's six writes give the entire exact seed
--   header consumed by actual Init182.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaInitialSeedHeader.lean#L72-L86
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaInitialSeedHeader.lean#L72-L86

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPrefixCommit
import Definitions.Def_Submission_ThreeSum_LightTernaryInitialBudgets
import Definitions.Def_Submission_Weighted_Global_LightTernaryArenaTemplate
import Definitions.Def_Submission_Weighted_Global_TernaryPrefixSeedHeader
import Definitions.Def_Submission_Weighted_Global_TernaryArenaInitialSeedHeader
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaInitialSeedHeader
open Light WeightedGlobalArenaLayout WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate
open LightWeightedGlobalSeedScoreFactory LightWeightedGlobalControllerFactory LightWeightedGlobalPrefixHeader LightWeightedGlobalPrefixFinish
set_option maxHeartbeats 4000000
set_option maxRecDepth 24000

theorem ThreeSum.WeightedGlobalArenaInitialSeedHeader.initialized {I : Input} {A : Inputs} {p q seed constants K bDigit n : ℕ}
    {μ ν : ℕ→ℤ}
    (hseed : seed=addr I.free I.capacity 2)
    (hconstants : seed+48≤constants)
    (hs : Seg μ seed (header (config p 0 I A 0) (q*q) 1 1 1 0 0 0 (addr I.free I.capacity 8)))
    (hb : Seg ν (seed+41) [1,1,1,((n*n:ℕ):ℤ),((n*n:ℕ):ℤ),
      (LightTernaryInitialBudgets.initial K bDigit n A.J I.requesterCount:ℤ)])
    (hk : ∀x,(x<seed+41 ∨ seed+47≤x)→(x<constants ∨ constants+3≤x)→ν x=μ x) :
    Seg ν seed (header (config p 0 I A 0) (q*q) 1 1 1 (n^2) (n^2)
      (LightTernaryInitialBudgets.initial K bDigit n A.J I.requesterCount) (addr I.free I.capacity 8)) := by sorry
