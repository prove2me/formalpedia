-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaHeaderAgreement_templateValues_actual
-- name    : ThreeSum.WeightedGlobalArenaHeaderAgreement.templateValues_actual
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T16:03:52.914852+00:00
-- url     : https://prove2.me/theorems/ecb1cfba-362e-4119-8eb5-c9cd936c36b9
-- title:
--   Weighted Global Arena Header Agreement: template Values actual
-- statement:
--   The Weighted Global Arena Header Agreement construction uses the template Values actual property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaHeaderAgreement.lean#L30-L37
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaHeaderAgreement.lean#L30-L37

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

theorem ThreeSum.WeightedGlobalArenaHeaderAgreement.templateValues_actual (I : Input) (inputs : List ℤ)
    (h3 : frame inputs 3=(I.nB:ℤ)) (h5 : frame inputs 5=(I.nC:ℤ))
    (h13 : frame inputs 13=(p:ℤ)) (h14 : frame inputs 14=((4^(fixedLength m):ℕ):ℤ))
    (h15 : frame inputs 15=(F:ℤ)) :
    LightWeightedGlobalArenaTemplate.hostValues (frame inputs) I.free I.capacity=templateValues I p m F := by sorry
