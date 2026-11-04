-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaCandidateGuardAllocation_resources
-- name    : ThreeSum.WeightedGlobalArenaCandidateGuardAllocation.resources
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T22:19:18.300202+00:00
-- url     : https://prove2.me/theorems/d6e147aa-ffe6-4152-ab98-d6377909ac29
-- title:
--   Weighted Global Arena Candidate Guard Allocation: resources
-- statement:
--   The fixed arena hardware need discharges every primitive candidate
--   resource guard, including the actual number of menu seeds.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaCandidateGuardAllocation.lean#L22-L54
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaCandidateGuardAllocation.lean#L22-L54

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaCandidateGuard
import Definitions.Def_Submission_Weighted_Global_TernaryArenaAllocationResources
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPrimitiveBounds
import Definitions.Def_Submission_Weighted_Global_TernaryArenaCandidateGuardAllocation
import Theorems.Thm_ThreeSum_WeightedFrontendResources_resources
import Theorems.Thm_ThreeSum_WeightedGlobalArenaFrontendResources_resources
import Theorems.Thm_ThreeSum_WeightedGlobalArenaSourceCountSeed_seed
import Theorems.Thm_ThreeSum_WeightedGlobalArenaSourceSeed_seed
import Theorems.Thm_ThreeSum_WeightedGlobalFrontendResources_resources

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaCandidateGuardAllocation
open Light WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps WeightedGlobalArenaLayout
open WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate WeightedGlobalArenaPrefixFootprints
open WeightedGlobalArenaAllocation LightWeightedGlobalSeedScoreFactory
variable {p m F r : ℕ} [Fact p.Prime]
set_option maxHeartbeats 6000000

theorem ThreeSum.WeightedGlobalArenaCandidateGuardAllocation.resources {lim : Limits} {depth K H M b drift scale n U seed positionCap : ℕ}
    (maps : Fin F→Weight m p) (τ cap : ℕ)
    (Alloc : Allocation maps τ cap M b K H drift scale)
    (I : Input) (A : Inputs) (D : Data (config p r I A seed))
    (hok : (WeightedGlobalArenaAllocationResources.need Alloc n U).Ok lim I.free depth)
    (hcap : I.capacity=capacity Alloc.D Alloc.E (n+U))
    (hr : r≤Nat.clog M (n^2)) (hJ : A.J=LightWeightedGlobalDimensions.J M b n U)
    (hnB : I.nB≤n) (hnC : I.nC≤n)
    (hO : I.requesterCount≤n*2^(LightWeightedGlobalDimensions.J M b n U))
    (hpos : positionCap≤n) (hB : D.bB<p) (hC : D.bC<p) (hOut : D.bO<p)
    (hseed : seed<(p^(LightWeightedGlobalDimensions.dim M b p K n U))^2) :
    WeightedGlobalArenaCandidateGuard.Resources (lim := lim) (depth := depth)
      (positionCap := positionCap) maps τ I A D := by sorry
