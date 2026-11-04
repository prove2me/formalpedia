-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaHeaderAgreement_templateValues_length
-- name    : ThreeSum.WeightedGlobalArenaHeaderAgreement.templateValues_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T16:10:37.641901+00:00
-- url     : https://prove2.me/theorems/c3f34181-fdc4-4a95-a36b-48a5b4625ea6
-- title:
--   Weighted Global Arena Header Agreement: template Values length
-- statement:
--   The Weighted Global Arena Header Agreement construction uses the template Values length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaHeaderAgreement.lean#L27-L28
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaHeaderAgreement.lean#L27-L28

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSourceSetup
import Definitions.Def_Submission_Weighted_Global_LightTernaryArenaTemplate
import Definitions.Def_Submission_Weighted_Global_TernaryPrefixHeaderSegment
import Definitions.Def_Submission_Weighted_Global_TernaryRepeatWordAddress
import Definitions.Def_Submission_Weighted_Global_DimensionBounds
import Definitions.Def_Submission_Weighted_Global_TernaryArenaHeaderAgreement
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaHeaderAgreement
open Light TernaryJointType WeightedGlobalLocalParameters WeightedGlobalArenaLayout WeightedGlobalArenaSourceSetup
set_option maxHeartbeats 8000000
set_option maxRecDepth 24000
variable {p m F : ℕ} [Fact p.Prime]

theorem ThreeSum.WeightedGlobalArenaHeaderAgreement.templateValues_length (I : Input) : (templateValues I p m F).length=106 := by sorry
