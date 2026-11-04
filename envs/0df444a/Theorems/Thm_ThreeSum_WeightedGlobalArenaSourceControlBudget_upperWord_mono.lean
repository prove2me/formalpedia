-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaSourceControlBudget_upperWord_mono
-- name    : ThreeSum.WeightedGlobalArenaSourceControlBudget.upperWord_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T16:10:48.023129+00:00
-- url     : https://prove2.me/theorems/c3d4a259-3301-44de-b4e1-bd7d620067d0
-- title:
--   Weighted Global Arena Source Control Budget: upper Word mono
-- statement:
--   The Weighted Global Arena Source Control Budget construction uses the upper Word mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaSourceControlBudget.lean#L62-L68
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaSourceControlBudget.lean#L62-L68

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSourceControls
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSourceControlBudget
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaSourceControlBudget
open Light WeightedGlobalArenaSourceSetup WeightedGlobalArenaSourceControls
open WeightedGlobalArenaPairMass WeightedGlobalLocalParameters WeightedGlobalNativeCompleteFrontend
open WeightedGlobalCoverGoodMaps StageBounds
variable {p m F r : ℕ} [Fact p.Prime]

theorem ThreeSum.WeightedGlobalArenaSourceControlBudget.upperWord_mono {m p F R r s n a w v : ℕ}
    (hp : 1≤p) (hF : 1≤F) (hR : 1≤R) (hr : r≤s) (hn : n≤a) (hw : w≤v) :
    upperWord m p F R r n w≤upperWord m p F R s a v := by sorry
