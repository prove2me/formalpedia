-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaSourceControlBudget_controls_of_budget
-- name    : ThreeSum.WeightedGlobalArenaSourceControlBudget.controls_of_budget
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T16:15:15.285325+00:00
-- url     : https://prove2.me/theorems/cfb715e7-1bd2-4309-b6c1-115bbdf5c8bf
-- title:
--   Weighted Global Arena Source Control Budget: controls of budget
-- statement:
--   The Weighted Global Arena Source Control Budget construction uses the controls of budget property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaSourceControlBudget.lean#L173-L181
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaSourceControlBudget.lean#L173-L181

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

theorem ThreeSum.WeightedGlobalArenaSourceControlBudget.controls_of_budget {lim : Limits} {d fr : ℕ}
    (maps : Fin F→Weight m p) (cap : ℕ) (I : Input) (right : Bool)
    (M n U W E : ℕ) (hM : 1<M) (hF : 1≤F) (hr : r≤Nat.clog M (n^2))
    (hn : (source (r := r) maps cap I right).NL≤n) (hweight : I.weightCap≤W*(U+1)^E)
    (h : (budget m p F (tableWidth maps cap+1) M W E n U).Ok lim fr d) :
    Controls (r := r) maps cap I right lim d := by sorry
