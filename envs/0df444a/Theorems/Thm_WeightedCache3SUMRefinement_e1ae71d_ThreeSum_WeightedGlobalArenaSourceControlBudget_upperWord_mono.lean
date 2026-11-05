-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaSourceControlBudget_upperWord_mono
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaSourceControlBudget.upperWord_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T13:09:10.473745+00:00
-- url     : https://prove2.me/theorems/1e16ea60-4903-46c3-b3e8-b22e44410c0e
-- title:
--   upperWord_mono
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryArenaSourceControlBudget.lean#L62-L68
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryArenaSourceControlBudget.lean#L62-L68

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

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaSourceControlBudget.upperWord_mono {m p F R r s n a w v : ℕ}
    (hp : 1≤p) (hF : 1≤F) (hR : 1≤R) (hr : r≤s) (hn : n≤a) (hw : w≤v) :
    upperWord m p F R r n w≤upperWord m p F R s a v := by sorry
