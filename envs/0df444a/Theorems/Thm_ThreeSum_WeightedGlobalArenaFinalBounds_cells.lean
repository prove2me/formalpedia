-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaFinalBounds_cells
-- name    : ThreeSum.WeightedGlobalArenaFinalBounds.cells
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T22:19:33.025716+00:00
-- url     : https://prove2.me/theorems/3c43c9bf-d478-4967-936f-b6480726ce9f
-- title:
--   Weighted Global Arena Final Bounds: cells
-- statement:
--   The Weighted Global Arena Final Bounds construction uses the cells property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaFinalBounds.lean#L32-L50
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaFinalBounds.lean#L32-L50

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

theorem ThreeSum.WeightedGlobalArenaFinalBounds.cells (maps : Fin F→Weight m p) (τ cap M b K H drift scale : ℕ)
    (I : Input) (n U : ℕ)
    (hO : I.requesterCount≤n*2^(LightWeightedGlobalDimensions.J M b n U)) :
    (2*H+1)*(entries (r := r) maps τ I).length≤
      (numbers maps τ cap M b K H drift scale n U r).reporterCells ∧
    2*H+1≤(numbers maps τ cap M b K H drift scale n U r).reporterCells ∧
    4*n+2≤(numbers maps τ cap M b K H drift scale n U r).reporterCells ∧
    (entries (r := r) maps τ I).length≤
      (numbers maps τ cap M b K H drift scale n U r).reporterCells := by sorry
