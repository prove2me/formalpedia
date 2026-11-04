-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaFinalBounds_words
-- name    : ThreeSum.WeightedGlobalArenaFinalBounds.words
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T22:19:33.271196+00:00
-- url     : https://prove2.me/theorems/456ddf9d-778f-4b34-9191-47d4ac9a6da4
-- title:
--   Weighted Global Arena Final Bounds: words
-- statement:
--   The Weighted Global Arena Final Bounds construction uses the words property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaFinalBounds.lean#L19-L30
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaFinalBounds.lean#L19-L30

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

theorem ThreeSum.WeightedGlobalArenaFinalBounds.words (maps : Fin F→Weight m p) (τ cap M b K H drift scale n U : ℕ) :
    (WeightedGlobalMomentDetectorResources.need (WeightedGlobalArenaPairMass.envelope maps cap M n) U H).word≤
      (numbers maps τ cap M b K H drift scale n U r).reporterWord ∧
    (WeightedGlobalMomentChannelResources.need (WeightedGlobalArenaPairMass.envelope maps cap M n) U (2*H)).word≤
      (numbers maps τ cap M b K H drift scale n U r).reporterWord := by sorry
