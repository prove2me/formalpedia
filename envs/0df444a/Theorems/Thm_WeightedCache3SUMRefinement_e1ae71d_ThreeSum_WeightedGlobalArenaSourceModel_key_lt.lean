-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaSourceModel_key_lt
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaSourceModel.key_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T13:29:48.728516+00:00
-- url     : https://prove2.me/theorems/2488ca93-3051-4951-9f31-c8d749c4e7d9
-- title:
--   key_lt
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryArenaSourceModel.lean#L47-L50
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryArenaSourceModel.lean#L47-L50

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaSourceSetup
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryCanonicalSourceBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaSourceModel
import Theorems.Thm_ThreeSum_LightSourceResidues_key_lt
import Theorems.Thm_ThreeSum_LightTernaryAppendKeys_key_lt

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaSourceModel
open TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps WeightedGlobalArenaSourceSetup
open TernaryCanonicalDictionaries WeightedGlobalNativeCompleteFrontend
attribute [local instance] Classical.propDecidable
variable {p m F r : ℕ} [Fact p.Prime]

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaSourceModel.key_lt (maps : Fin F→Weight m p) (cap : ℕ) (I : Input) (right : Bool)
    (j : Index (r := r) maps cap right) :
    (source (r := r) maps cap I right).key j.val<(source (r := r) maps cap I right).bank := by sorry
