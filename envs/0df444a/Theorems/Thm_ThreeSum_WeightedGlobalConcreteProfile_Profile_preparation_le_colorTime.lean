-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalConcreteProfile_Profile_preparation_le_colorTime
-- name    : ThreeSum.WeightedGlobalConcreteProfile.Profile.preparation_le_colorTime
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T00:46:00.949209+00:00
-- url     : https://prove2.me/theorems/0631524d-1a08-427b-8e5d-80fbb7af0ee6
-- title:
--   Profile: preparation le color Time
-- statement:
--   The Profile construction uses the preparation le color Time property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryProfileRuntime.lean#L33-L41
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryProfileRuntime.lean#L33-L41

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

theorem ThreeSum.WeightedGlobalConcreteProfile.Profile.preparation_le_colorTime (P : Profile κ) (n : ℕ) :
    LightWeightedGlobalColorPreparationProof.time n
      (LightWeightedGlobalDimensions.J P.M P.radix n (n^κ)) (n^κ)+
      LightWeightedGlobalArenaTemplate.time P.allocation.E+LightTernaryInitialBudgets.time P.K+10000≤
        P.colorTime n := by sorry
