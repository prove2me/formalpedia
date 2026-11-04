-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaHeaderAgreement_output_rank
-- name    : ThreeSum.WeightedGlobalArenaHeaderAgreement.output_rank
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T15:53:46.099633+00:00
-- url     : https://prove2.me/theorems/0a4ce3dc-998d-4c53-9743-4df9dee48d60
-- title:
--   Weighted Global Arena Header Agreement: output rank
-- statement:
--   The Weighted Global Arena Header Agreement construction uses the output rank property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaHeaderAgreement.lean#L39-L45
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaHeaderAgreement.lean#L39-L45

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSourceSetup
import Definitions.Def_Submission_Weighted_Global_LightTernaryArenaTemplate
import Definitions.Def_Submission_Weighted_Global_TernaryPrefixHeaderSegment
import Definitions.Def_Submission_Weighted_Global_TernaryRepeatWordAddress
import Definitions.Def_Submission_Weighted_Global_DimensionBounds
import Definitions.Def_Submission_Weighted_Global_TernaryArenaHeaderAgreement
import Theorems.Thm_ThreeSum_TernaryDimensionBounds_output_rank
import Theorems.Thm_ThreeSum_WeightedGlobalDimensionBounds_output_rank
import Theorems.Thm_ThreeSum_WeightedSchedule_output_rank

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaHeaderAgreement
open Light TernaryJointType WeightedGlobalLocalParameters WeightedGlobalArenaLayout WeightedGlobalArenaSourceSetup
set_option maxHeartbeats 8000000
set_option maxRecDepth 24000
variable {p m F : ℕ} [Fact p.Prime]

theorem ThreeSum.WeightedGlobalArenaHeaderAgreement.output_rank (Q : WeightedGlobalGoodOutputCatalog.Output m) (r : ℕ) :
    WeightedGlobalBank.rank (WeightedGlobalRepeatedWords.canonical (fun _ : Fin r=>Q.val))=2*(alphaRank m*r) := by sorry
