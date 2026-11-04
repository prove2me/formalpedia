-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaCandidateScoreBounds_collision_le
-- name    : ThreeSum.WeightedGlobalArenaCandidateScoreBounds.collision_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T22:18:56.51869+00:00
-- url     : https://prove2.me/theorems/aad85194-398f-448a-9a75-6fdc972804d2
-- title:
--   Weighted Global Arena Candidate Score Bounds: collision le
-- statement:
--   The Weighted Global Arena Candidate Score Bounds construction uses the collision le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaCandidateScoreBounds.lean#L109-L116
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaCandidateScoreBounds.lean#L109-L116

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

theorem ThreeSum.WeightedGlobalArenaCandidateScoreBounds.collision_le {a : ℕ} (f : Fin a→ℕ) :
    |((TernaryOriginalCollisions.collisionPairs f).card : ℤ)|≤(a^2 : ℕ) := by sorry
