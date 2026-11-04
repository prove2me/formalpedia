-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaSelectorAllocation_initial_le
-- name    : ThreeSum.WeightedGlobalArenaSelectorAllocation.initial_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T22:24:43.903684+00:00
-- url     : https://prove2.me/theorems/c84b23b0-b525-4d31-b286-a21702c51a83
-- title:
--   Weighted Global Arena Selector Allocation: initial le
-- statement:
--   Runtime thresholds use the actual requester count. The larger monotone
--   initial-word expression in the fixed footprint bounds this value.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaSelectorAllocation.lean#L40-L49
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaSelectorAllocation.lean#L40-L49

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaCandidateScoreBounds
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSelectorAllocation
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaSelectorAllocation
open Light WeightedGlobalArenaPrefixFootprints WeightedGlobalArenaAllocation WeightedGlobalArenaLayout
open WeightedGlobalCoverGoodMaps WeightedGlobalLocalParameters
variable {p m F : ℕ} [Fact p.Prime]
set_option maxHeartbeats 6000000

theorem ThreeSum.WeightedGlobalArenaSelectorAllocation.initial_le {K b n J nO nO' : ℕ} (hO : nO≤nO') (a drift scale : ℕ) :
    LightTernaryInitialBudgets.initial K b n J nO≤
      LightTernaryInitialBudgets.word K b a drift scale n J nO' := by sorry
