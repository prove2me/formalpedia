-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaCandidateScoreBounds_paired_le
-- name    : ThreeSum.WeightedGlobalArenaCandidateScoreBounds.paired_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T22:18:52.939008+00:00
-- url     : https://prove2.me/theorems/7921826c-4dba-43f8-aadd-63b87808ae08
-- title:
--   Weighted Global Arena Candidate Score Bounds: paired le
-- statement:
--   Every literal physical pair and ordered K-tuple is retained in this bound.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaCandidateScoreBounds.lean#L23-L57
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaCandidateScoreBounds.lean#L23-L57

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaCandidateGuard
import Definitions.Def_Submission_Weighted_Global_TernaryArenaTensorBounds
import Definitions.Def_Submission_Weighted_Global_TernaryArenaAllocationResources
import Definitions.Def_Submission_Weighted_Global_TernaryArenaCandidateScoreBounds
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

theorem ThreeSum.WeightedGlobalArenaCandidateScoreBounds.paired_le {N : ℕ} (S : WeightedSourceCountExecutionFactory.Setup N)
    (K J tag : ℕ) (L R : ℕ→ℕ→ℤ)
    (hL : ∀ i<S.left.NL, ∀ a<J+2, (L i a).natAbs≤tag)
    (hR : ∀ i<S.right.NL, ∀ a<J+2, (R i a).natAbs≤tag) :
    pairedPotential S K J L R≤
      S.front.count*(pairBound S)^K*(J+2)^(2*K)*(((2*K).factorial*tag^(2*K))^2) := by sorry
