-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalColoredSolverNeed_polyNeed_power
-- name    : ThreeSum.WeightedGlobalColoredSolverNeed.polyNeed_power
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T22:22:13.708073+00:00
-- url     : https://prove2.me/theorems/6d98f66a-b526-4c81-84c2-9f06c7813ac3
-- title:
--   Weighted Global Colored Solver Need: poly Need power
-- statement:
--   The Weighted Global Colored Solver Need construction uses the poly Need power property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColoredSolverNeed.lean#L227-L243
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColoredSolverNeed.lean#L227-L243

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaAllocationResources
import Definitions.Def_Submission_Weighted_Global_LightTernaryColorPreparationProof
import Definitions.Def_Submission_ThreeSum_TernaryColorPreludeResources_w3sum_ac885d1
import Definitions.Def_Submission_Weighted_Global_TernaryColoredSolverNeed
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalColoredSolverNeed
open Light WeightedGlobalArenaLayout WeightedGlobalArenaAllocation WeightedGlobalArenaPrefixFootprints
open WeightedGlobalCoverGoodMaps WeightedGlobalLocalParameters LightWeightedGlobalColorPreparation
set_option maxHeartbeats 500000
set_option maxRecDepth 24000
variable {p m F : ℕ} [Fact p.Prime]

theorem ThreeSum.WeightedGlobalColoredSolverNeed.polyNeed_power {f : ℕ→ℕ→Need} (hf : PolyNeed f) (κ : ℕ) :
    PolyNeed (fun n _U=>f n (n^κ)) := by sorry
