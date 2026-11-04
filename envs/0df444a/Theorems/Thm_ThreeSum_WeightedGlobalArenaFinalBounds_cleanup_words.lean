-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaFinalBounds_cleanup_words
-- name    : ThreeSum.WeightedGlobalArenaFinalBounds.cleanup_words
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T22:19:38.112984+00:00
-- url     : https://prove2.me/theorems/a88bbb5d-93ac-4f1f-9256-bd7cfd597fce
-- title:
--   Weighted Global Arena Final Bounds: cleanup words
-- statement:
--   The Weighted Global Arena Final Bounds construction uses the cleanup words property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaFinalBounds.lean#L99-L110
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaFinalBounds.lean#L99-L110

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

theorem ThreeSum.WeightedGlobalArenaFinalBounds.cleanup_words (maps : Fin F→Weight m p) (τ cap M b K H drift scale n U : ℕ) :
    2*n+2^(2*N m r+1)+16≤(numbers maps τ cap M b K H drift scale n U r).reporterWord ∧
    n*n+n+p^r+16≤(numbers maps τ cap M b K H drift scale n U r).reporterWord ∧
    2*U+3≤(numbers maps τ cap M b K H drift scale n U r).reporterWord := by sorry
