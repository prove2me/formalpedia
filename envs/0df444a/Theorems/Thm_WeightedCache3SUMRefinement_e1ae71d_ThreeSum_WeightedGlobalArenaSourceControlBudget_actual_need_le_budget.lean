-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaSourceControlBudget_actual_need_le_budget
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaSourceControlBudget.actual_need_le_budget
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T13:12:11.321034+00:00
-- url     : https://prove2.me/theorems/b279c0f1-b7f5-4d22-ade6-02bf86bb3dc6
-- title:
--   actual_need_le_budget
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryArenaSourceControlBudget.lean#L150-L171
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryArenaSourceControlBudget.lean#L150-L171

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaSourceControls
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaSourceControlBudget
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaSourceControlBudget
open Light WeightedGlobalArenaSourceSetup WeightedGlobalArenaSourceControls
open WeightedGlobalArenaPairMass WeightedGlobalLocalParameters WeightedGlobalNativeCompleteFrontend
open WeightedGlobalCoverGoodMaps StageBounds
variable {p m F r : ℕ} [Fact p.Prime]

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaSourceControlBudget.actual_need_le_budget (maps : Fin F→Weight m p) (cap : ℕ) (I : Input) (right : Bool)
    (M n U W E : ℕ) (hM : 1<M) (hF : 1≤F) (hr : r≤Nat.clog M (n^2))
    (hn : (source (r := r) maps cap I right).NL≤n) (hweight : I.weightCap≤W*(U+1)^E) :
    (need (r := r) maps cap I right).word≤
        (budget m p F (tableWidth maps cap+1) M W E n U).word ∧
    (need (r := r) maps cap I right).depth≤
        (budget m p F (tableWidth maps cap+1) M W E n U).depth := by sorry
