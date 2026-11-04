-- Prove2me | Theorems.Thm_ThreeSum_WeightedBankStageModel_min_one
-- name    : ThreeSum.WeightedBankStageModel.min_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:21:17.029046+00:00
-- url     : https://prove2.me/theorems/36486289-67ea-48bc-a6e1-4a30e836f76f
-- title:
--   Weighted Bank Stage Model: min one
-- statement:
--   The Weighted Bank Stage Model construction uses the min one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/BankStageModel.lean#L38-L39
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/BankStageModel.lean#L38-L39

import Definitions.Def_Submission_Weighted_Cache
import Definitions.Def_Submission_ThreeSum_TernaryFrozenQueryStages
import Definitions.Def_Submission_ThreeSum_TernaryTransform
import Definitions.Def_Submission_ThreeSum_LightTernaryMetadata
import Definitions.Def_Submission_ThreeSum_LightTernaryPass
import Definitions.Def_Submission_ThreeSum_LightTernaryInversePass
import Definitions.Def_Submission_Weighted_BankStageModel
set_option autoImplicit false
open ThreeSum ThreeSum.WeightedBankStageModel
open ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryQuery
open ThreeSum.TernaryCodeSemantics ThreeSum.TernaryFrozenQueryStages
set_option maxHeartbeats 3000000

theorem ThreeSum.WeightedBankStageModel.min_one (q : Fin 3) : min (1 : Fin 3) q=clampOne q := by sorry
