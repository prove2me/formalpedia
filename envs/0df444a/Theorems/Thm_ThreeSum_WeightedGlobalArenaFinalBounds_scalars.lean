-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaFinalBounds_scalars
-- name    : ThreeSum.WeightedGlobalArenaFinalBounds.scalars
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T22:19:37.608203+00:00
-- url     : https://prove2.me/theorems/a8b2ce03-a1b6-4e66-a090-4627b6e7a35f
-- title:
--   Weighted Global Arena Final Bounds: scalars
-- statement:
--   The fourth-power allocation pays the entire finite runtime argument
--   list, including all source and bank scalars.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaFinalBounds.lean#L72-L97
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaFinalBounds.lean#L72-L97

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaFrontBounds
import Definitions.Def_Submission_Weighted_Global_TernaryArenaArgumentBudget
import Definitions.Def_Submission_Weighted_Global_TernaryArenaAllocationResources
import Definitions.Def_Submission_Weighted_Global_TernaryArenaFinalBounds
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaFinalBounds
open Light WeightedGlobalArenaLayout WeightedGlobalArenaSourceSetup WeightedGlobalArenaPrefixFootprints
open WeightedGlobalCoverGoodMaps WeightedGlobalLocalParameters
set_option maxHeartbeats 8000000
variable {p m F r : ℕ} [Fact p.Prime]

theorem ThreeSum.WeightedGlobalArenaFinalBounds.scalars (maps : Fin F→Weight m p) (τ cap M b K H drift scale : ℕ)
    (I : Input) (n U : ℕ)
    (hO : I.requesterCount≤n*2^(LightWeightedGlobalDimensions.J M b n U)) :
    WeightedGlobalArenaArgumentWords.scalarControl m p F r (entries (r := r) maps τ I).length≤
      WeightedGlobalArenaPrefixFootprints.envelope maps τ cap M b K H drift scale n U r := by sorry
