-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaCandidateScoreBounds_actual_score_bound
-- name    : ThreeSum.WeightedGlobalArenaCandidateScoreBounds.actual_score_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T22:17:31.13494+00:00
-- url     : https://prove2.me/theorems/db8bcb09-964f-4639-825f-0d64b1d402b1
-- title:
--   Weighted Global Arena Candidate Score Bounds: actual score bound
-- statement:
--   The Weighted Global Arena Candidate Score Bounds construction uses the actual score bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaCandidateScoreBounds.lean#L59-L107
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaCandidateScoreBounds.lean#L59-L107

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

theorem ThreeSum.WeightedGlobalArenaCandidateScoreBounds.actual_score_bound (maps : Fin F→Weight m p) (τ cap M b K H drift scale tag : ℕ)
    (Q : WeightedGlobalGoodOutputCatalog.Output m) (I : Input) (A : Inputs) (seed n U : ℕ)
    (D : Data (config p r I A seed)) (L R : ℕ→ℕ→ℤ)
    (hJ : A.J=LightWeightedGlobalDimensions.J M b n U)
    (hnB : I.nB≤n) (hnC : I.nC≤n)
    (hO : I.requesterCount≤n*2^(LightWeightedGlobalDimensions.J M b n U))
    (htag : tag≤2*(4^fixedLength m)+1)
    (hL : ∀i<I.nB,∀a<A.J+2,(L i a).natAbs≤tag)
    (hR : ∀i<I.nC,∀a<A.J+2,(R i a).natAbs≤tag) :
    |(WeightedGlobalArenaCandidateGuard.actual maps τ cap tag Q I A seed D L R).score K|≤
      ((numbers maps τ cap M b K H drift scale n U r).candidateScore : ℤ) := by sorry
