-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedGlobalSeedScoreFactory_Data_flag_eq_one
-- name    : ThreeSum.LightWeightedGlobalSeedScoreFactory.Data.flag_eq_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T15:18:55.11727+00:00
-- url     : https://prove2.me/theorems/ef7fbfe2-88fc-4d61-8c42-f30cc94db01d
-- title:
--   Data: flag eq one
-- statement:
--   The Data construction uses the flag eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernarySeedScoreFactory.lean#L501-L505
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernarySeedScoreFactory.lean#L501-L505

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernarySeedScore
import Definitions.Def_Submission_ThreeSum_TernaryPhysicalDigitSpan
import Definitions.Def_Submission_ThreeSum_TernaryWantedBatchCount
import Definitions.Def_Submission_Weighted_Global_LightTernaryTensorFactoryScaled
import Definitions.Def_Submission_Weighted_Global_TernaryNativeTensorScore
import Definitions.Def_Submission_Weighted_Global_LightTernarySeedScoreFactory
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightWeightedGlobalSeedScoreFactory
open Light
set_option maxHeartbeats 8000000
set_option maxRecDepth 24000
variable {lim : Limits}
open scoped BigOperators

theorem ThreeSum.LightWeightedGlobalSeedScoreFactory.Data.flag_eq_one {C : Config} [Fact C.p.Prime] (D : Data C) :
    D.flag=1 ↔ D.logicalRow∉TernaryPhysicalDigitSpan.forbidden D.logicalRows := by sorry
