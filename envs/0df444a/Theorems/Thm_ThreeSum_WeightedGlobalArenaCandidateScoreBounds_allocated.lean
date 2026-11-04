-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaCandidateScoreBounds_allocated
-- name    : ThreeSum.WeightedGlobalArenaCandidateScoreBounds.allocated
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T22:13:39.106196+00:00
-- url     : https://prove2.me/theorems/9a12fbe7-1488-4073-8bfb-f69e5ad1fd50
-- title:
--   Weighted Global Arena Candidate Score Bounds: allocated
-- statement:
--   Allocation's fixed hardware need supplies the selector's common score
--   cap and the candidate paired-score word guard.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaCandidateScoreBounds.lean#L154-L178
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaCandidateScoreBounds.lean#L154-L178

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaCandidateGuard
import Definitions.Def_Submission_Weighted_Global_TernaryArenaTensorBounds
import Definitions.Def_Submission_Weighted_Global_TernaryArenaAllocationResources
import Definitions.Def_Submission_Weighted_Global_TernaryArenaCandidateScoreBounds
import Theorems.Thm_ThreeSum_WeightedGlobalArenaFrontBounds_capacity
import Theorems.Thm_ThreeSum_WeightedGlobalArenaSourceCountSeed_seed
import Theorems.Thm_ThreeSum_WeightedGlobalArenaSourceSeed_seed

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaCandidateScoreBounds
open WeightedGlobalNativePairMoments WeightedGlobalNativeMomentBounds WeightedGlobalNativeTensorScore
open WeightedGlobalArenaPrefixFootprints WeightedGlobalArenaSourceSetup WeightedGlobalArenaSourceBounds
open WeightedGlobalArenaSeedCandidate LightWeightedGlobalSeedScoreFactory
open WeightedGlobalCoverGoodMaps WeightedGlobalLocalParameters WeightedGlobalNativeCompleteFrontend
open scoped BigOperators
variable {p m F r : ℕ} [Fact p.Prime]
set_option maxHeartbeats 6000000

theorem ThreeSum.WeightedGlobalArenaCandidateScoreBounds.allocated {lim : Light.Limits} {depth : ℕ}
    (maps : Fin F→Weight m p) (τ cap M b K H drift scale tag : ℕ)
    (Alloc : WeightedGlobalArenaAllocation.Allocation maps τ cap M b K H drift scale)
    (Q : WeightedGlobalGoodOutputCatalog.Output m) (I : Input) (A : Inputs) (seed n U : ℕ)
    (D : Data (config p r I A seed)) (L R : ℕ→ℕ→ℤ)
    (hok : (WeightedGlobalArenaAllocationResources.need Alloc n U).Ok lim I.free depth)
    (hcap : I.capacity=WeightedGlobalArenaLayout.capacity Alloc.D Alloc.E (n+U))
    (hr : r≤Nat.clog M (n^2))
    (hJ : A.J=LightWeightedGlobalDimensions.J M b n U)
    (hnB : I.nB≤n) (hnC : I.nC≤n)
    (hO : I.requesterCount≤n*2^(LightWeightedGlobalDimensions.J M b n U))
    (htag : tag≤2*(4^fixedLength m)+1)
    (hL : ∀i<I.nB,∀a<A.J+2,|L i a|≤(tag : ℤ))
    (hR : ∀i<I.nC,∀a<A.J+2,|R i a|≤(tag : ℤ)) :
    |D.collisionB|≤(I.capacity : ℤ) ∧ |D.collisionC|≤(I.capacity : ℤ) ∧
    |(WeightedGlobalArenaCandidateGuard.actual maps τ cap tag Q I A seed D L R).score K|≤(I.capacity : ℤ) ∧
    (I.capacity : ℤ)≤lim.word := by sorry
