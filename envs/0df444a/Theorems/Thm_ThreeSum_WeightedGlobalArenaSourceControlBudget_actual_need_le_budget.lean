-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaSourceControlBudget_actual_need_le_budget
-- name    : ThreeSum.WeightedGlobalArenaSourceControlBudget.actual_need_le_budget
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T16:14:42.420327+00:00
-- url     : https://prove2.me/theorems/7a73dfd7-e9e2-4e68-855a-2fe66197f84d
-- title:
--   Weighted Global Arena Source Control Budget: actual need le budget
-- statement:
--   The Weighted Global Arena Source Control Budget construction uses the actual need le budget property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaSourceControlBudget.lean#L150-L171
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaSourceControlBudget.lean#L150-L171

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

theorem ThreeSum.WeightedGlobalArenaSourceControlBudget.actual_need_le_budget (maps : Fin F→Weight m p) (cap : ℕ) (I : Input) (right : Bool)
    (M n U W E : ℕ) (hM : 1<M) (hF : 1≤F) (hr : r≤Nat.clog M (n^2))
    (hn : (source (r := r) maps cap I right).NL≤n) (hweight : I.weightCap≤W*(U+1)^E) :
    (need (r := r) maps cap I right).word≤
        (budget m p F (tableWidth maps cap+1) M W E n U).word ∧
    (need (r := r) maps cap I right).depth≤
        (budget m p F (tableWidth maps cap+1) M W E n U).depth := by sorry
