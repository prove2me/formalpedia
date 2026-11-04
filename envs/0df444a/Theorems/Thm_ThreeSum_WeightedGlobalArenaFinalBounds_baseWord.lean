-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaFinalBounds_baseWord
-- name    : ThreeSum.WeightedGlobalArenaFinalBounds.baseWord
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T22:16:14.464242+00:00
-- url     : https://prove2.me/theorems/70090c03-a2e4-436a-923a-a533817bd5d2
-- title:
--   Weighted Global Arena Final Bounds: base Word
-- statement:
--   The Weighted Global Arena Final Bounds construction uses the base Word property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaFinalBounds.lean#L52-L68
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaFinalBounds.lean#L52-L68

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

theorem ThreeSum.WeightedGlobalArenaFinalBounds.baseWord (maps : Fin F→Weight m p) (τ cap M b K H drift scale n U : ℕ) :
    WeightedGlobalArenaSourceControlBudget.baseWord m p F r≤
      (numbers maps τ cap M b K H drift scale n U r).sourceWord := by sorry
