-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaSourceControlBudget_actual_word_le
-- name    : ThreeSum.WeightedGlobalArenaSourceControlBudget.actual_word_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T16:19:24.852137+00:00
-- url     : https://prove2.me/theorems/4fc177c4-2414-4063-b48c-354fea06e638
-- title:
--   Weighted Global Arena Source Control Budget: actual word le
-- statement:
--   The Weighted Global Arena Source Control Budget construction uses the actual word le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaSourceControlBudget.lean#L39-L60
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaSourceControlBudget.lean#L39-L60

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

theorem ThreeSum.WeightedGlobalArenaSourceControlBudget.actual_word_le (maps : Fin F→Weight m p) (cap : ℕ) (I : Input) (right : Bool)
    (n : ℕ) (hn : (source (r := r) maps cap I right).NL≤n) :
    word (r := r) maps cap I right≤
      upperWord m p F (tableWidth maps cap+1) r n I.weightCap := by sorry
