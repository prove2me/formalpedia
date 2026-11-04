-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaGuardTransport_primitive
-- name    : ThreeSum.WeightedGlobalArenaGuardTransport.primitive
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T21:33:17.63987+00:00
-- url     : https://prove2.me/theorems/98206710-706e-4c50-bb8e-8d397b45a276
-- title:
--   Weighted Global Arena Guard Transport: primitive
-- statement:
--   Only immutable original arrays, old key slots4..6 and catalog7 are
--   read by the primitive guards. Four score arrays and host104 are excluded.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaGuardTransport.lean#L41-L81
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaGuardTransport.lean#L41-L81

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaCandidateGuard
import Definitions.Def_Submission_Weighted_Global_TernaryArenaScoreScan
import Definitions.Def_Submission_Weighted_Global_LightTernaryControllerFull
import Definitions.Def_Submission_Weighted_Global_TernaryArenaGuardTransport
import Theorems.Thm_ThreeSum_WeightedGlobalArenaSourceCountSeed_seed
import Theorems.Thm_ThreeSum_WeightedGlobalArenaSourceSeed_seed

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaGuardTransport
open Light TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps
open WeightedGlobalArenaSourceSetup WeightedGlobalNativeCompleteFrontend WeightedGlobalArenaLayout
open LightWeightedGlobalSeedScoreFactory WeightedGlobalArenaSeedCandidate WeightedGlobalArenaScoreScan
variable {p m F r : ℕ} [Fact p.Prime]
set_option maxHeartbeats 6000000
set_option maxRecDepth 24000

theorem ThreeSum.WeightedGlobalArenaGuardTransport.primitive {I : Input} {A : Inputs} {seed positionCap : ℕ}
    {D : Data (config p r I A seed)} {μ ν : ℕ→ℤ}
    (M : WeightedGlobalArenaSeedPrimitiveGuards.Reads I A seed D μ positionCap)
    (h : KeepInputs I μ ν) (hC : 106≤I.capacity)
    (hnB : I.nB≤I.capacity) (hnC : I.nC≤I.capacity)
    (hnO : I.requesterCount≤I.capacity) (hspan : A.J*p^(r-1)≤I.capacity) :
    WeightedGlobalArenaSeedPrimitiveGuards.Reads I A seed D ν positionCap := by sorry
