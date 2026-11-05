-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalConcreteProfile_Profile_hybrid_time_target
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalConcreteProfile.Profile.hybrid_time_target
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T19:37:15.200789+00:00
-- url     : https://prove2.me/theorems/9ff2d1df-ebc5-4922-b6d0-03e06cd71731
-- title:
--   hybrid_time_target
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryProfileRuntime.lean#L71-L75
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryProfileRuntime.lean#L71-L75

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryConcreteProfile
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryActualGlobalQueryRuntime
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryFastProgramBudget
import Definitions.Def_Submission_ThreeSum_TernarySolverEndBridge
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryProfileRuntime
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalConcreteProfile WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalConcreteProfile.Profile
open Light StageBounds WeightedGlobalLocalParameters WeightedGlobalActualColoredRuntime
open WeightedGlobalActualPrefixRuntime WeightedGlobalOversizeOverhead Filter
open scoped Topology
set_option maxHeartbeats 5000000
set_option maxRecDepth 24000
variable {κ : ℕ}

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalConcreteProfile.Profile.hybrid_time_target (P : Profile κ) :
    ∀ᶠ n : ℕ in atTop,
      timeUpTo P.hybridTime n ((n:ℝ)^(κ:ℝ))≤(n:ℝ)^(384055881637/200000000000:ℝ) := by sorry
