-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaSourceModel_group_spec
-- name    : ThreeSum.WeightedGlobalArenaSourceModel.group_spec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T16:10:16.162185+00:00
-- url     : https://prove2.me/theorems/82cc7615-e8f0-4b08-bfe1-a698a7c35f06
-- title:
--   Weighted Global Arena Source Model: group spec
-- statement:
--   The Weighted Global Arena Source Model construction uses the group spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaSourceModel.lean#L38-L45
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaSourceModel.lean#L38-L45

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSourceSetup
import Definitions.Def_Submission_Weighted_Global_TernaryCanonicalSourceBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSourceModel
import Theorems.Thm_Light_Ends_block

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaSourceModel
open TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps WeightedGlobalArenaSourceSetup
open TernaryCanonicalDictionaries WeightedGlobalNativeCompleteFrontend
attribute [local instance] Classical.propDecidable
variable {p m F r : ℕ} [Fact p.Prime]

theorem ThreeSum.WeightedGlobalArenaSourceModel.group_spec (maps : Fin F→Weight m p) (cap : ℕ) (I : Input) (right : Bool)
    (j : Index (r := r) maps cap right) :
    (source (r := r) maps cap I right).group j.val=
      WeightedGlobalNativeBlockPairs.occurrenceCode
        (fun i => (WeightedGlobalCanonicalSourceBank.block right maps cap j i).1) := by sorry
