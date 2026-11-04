-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaCandidateGuardAllocation_new_span
-- name    : ThreeSum.WeightedGlobalArenaCandidateGuardAllocation.new_span
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T22:18:08.692251+00:00
-- url     : https://prove2.me/theorems/1257a01a-29e3-4f35-9908-0ce06f43a997
-- title:
--   Weighted Global Arena Candidate Guard Allocation: new span
-- statement:
--   The span commit stores only the digit restriction and fits the next
--   prefix catalog in one padded slot.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaCandidateGuardAllocation.lean#L58-L68
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaCandidateGuardAllocation.lean#L58-L68

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaCandidateGuard
import Definitions.Def_Submission_Weighted_Global_TernaryArenaAllocationResources
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPrimitiveBounds
import Definitions.Def_Submission_Weighted_Global_TernaryArenaCandidateGuardAllocation
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaCandidateGuardAllocation
open Light WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps WeightedGlobalArenaLayout
open WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate WeightedGlobalArenaPrefixFootprints
open WeightedGlobalArenaAllocation LightWeightedGlobalSeedScoreFactory
variable {p m F r : ℕ} [Fact p.Prime]
set_option maxHeartbeats 6000000

theorem ThreeSum.WeightedGlobalArenaCandidateGuardAllocation.new_span (maps : Fin F→Weight m p) (τ cap M b K H drift scale n U : ℕ)
    (I : Input) (A : Inputs) (hr : 0<r)
    (hJ : A.J=LightWeightedGlobalDimensions.J M b n U)
    (HC : Fits I.capacity (numbers maps τ cap M b K H drift scale n U r)) :
    A.J*p^(r-1)*p≤I.capacity := by sorry
