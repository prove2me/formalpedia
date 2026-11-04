-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalConcreteProfile_Profile_hybrid_time_target
-- name    : ThreeSum.WeightedGlobalConcreteProfile.Profile.hybrid_time_target
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T00:31:18.012212+00:00
-- url     : https://prove2.me/theorems/ebd00c61-d251-45b9-a15a-ea5c82def871
-- title:
--   Profile: hybrid time target
-- statement:
--   The Profile construction uses the hybrid time target property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryProfileRuntime.lean#L71-L75
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryProfileRuntime.lean#L71-L75

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryConcreteProfile
import Definitions.Def_Submission_Weighted_Global_TernaryActualGlobalQueryRuntime
import Definitions.Def_Submission_Weighted_Global_TernaryFastProgramBudget
import Definitions.Def_Submission_ThreeSum_TernarySolverEndBridge
import Definitions.Def_Submission_Weighted_Global_TernaryProfileRuntime
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalConcreteProfile ThreeSum.WeightedGlobalConcreteProfile.Profile
open Light StageBounds WeightedGlobalLocalParameters WeightedGlobalActualColoredRuntime
open WeightedGlobalActualPrefixRuntime WeightedGlobalOversizeOverhead Filter
open scoped Topology
set_option maxHeartbeats 5000000
set_option maxRecDepth 24000
variable {κ : ℕ}

theorem ThreeSum.WeightedGlobalConcreteProfile.Profile.hybrid_time_target (P : Profile κ) :
    ∀ᶠ n : ℕ in atTop,
      timeUpTo P.hybridTime n ((n:ℝ)^(κ:ℝ))≤(n:ℝ)^(96013971/50000000:ℝ) := by sorry
