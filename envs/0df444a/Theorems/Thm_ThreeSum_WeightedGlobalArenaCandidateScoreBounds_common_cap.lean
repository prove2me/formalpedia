-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaCandidateScoreBounds_common_cap
-- name    : ThreeSum.WeightedGlobalArenaCandidateScoreBounds.common_cap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T22:20:05.872992+00:00
-- url     : https://prove2.me/theorems/4f261285-bce7-4c11-915f-8d3a9b1d2bab
-- title:
--   Weighted Global Arena Candidate Score Bounds: common cap
-- statement:
--   One explicit score cap covers both original collision scores and the
--   scaled, fully repeated physical paired potential.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaCandidateScoreBounds.lean#L120-L150
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaCandidateScoreBounds.lean#L120-L150

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaCandidateGuard
import Definitions.Def_Submission_Weighted_Global_TernaryArenaTensorBounds
import Definitions.Def_Submission_Weighted_Global_TernaryArenaAllocationResources
import Definitions.Def_Submission_Weighted_Global_TernaryArenaCandidateScoreBounds
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

theorem ThreeSum.WeightedGlobalArenaCandidateScoreBounds.common_cap (maps : Fin F→Weight m p) (τ cap M b K H drift scale tag : ℕ)
    (Q : WeightedGlobalGoodOutputCatalog.Output m) (I : Input) (A : Inputs) (seed n U : ℕ)
    (D : Data (config p r I A seed)) (L R : ℕ→ℕ→ℤ)
    (hJ : A.J=LightWeightedGlobalDimensions.J M b n U)
    (hnB : I.nB≤n) (hnC : I.nC≤n)
    (hO : I.requesterCount≤n*2^(LightWeightedGlobalDimensions.J M b n U))
    (htag : tag≤2*(4^fixedLength m)+1)
    (hL : ∀i<I.nB,∀a<A.J+2,|L i a|≤(tag : ℤ))
    (hR : ∀i<I.nC,∀a<A.J+2,|R i a|≤(tag : ℤ)) :
    |D.collisionB|≤((numbers maps τ cap M b K H drift scale n U r).candidateScore : ℤ) ∧
    |D.collisionC|≤((numbers maps τ cap M b K H drift scale n U r).candidateScore : ℤ) ∧
    |(WeightedGlobalArenaCandidateGuard.actual maps τ cap tag Q I A seed D L R).score K|≤
      ((numbers maps τ cap M b K H drift scale n U r).candidateScore : ℤ) := by sorry
