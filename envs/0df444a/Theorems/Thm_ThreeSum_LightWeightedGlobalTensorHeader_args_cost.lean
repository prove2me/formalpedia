-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedGlobalTensorHeader_args_cost
-- name    : ThreeSum.LightWeightedGlobalTensorHeader.args_cost
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:43:46.937206+00:00
-- url     : https://prove2.me/theorems/436b594e-0fa5-4d57-99af-72ecd3d339a6
-- title:
--   Light Weighted Global Tensor Header: args cost
-- statement:
--   The Light Weighted Global Tensor Header construction uses the args cost property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryTensorHeader.lean#L38-L39
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryTensorHeader.lean#L38-L39

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryTensorDriverSyntax
import Definitions.Def_Submission_Weighted_Global_LightTernaryTensorHeader
set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightedGlobalTensorHeader
open Light LightWeightedGlobalTensorDriver

theorem ThreeSum.LightWeightedGlobalTensorHeader.args_cost : (countArgs.map Expr.cost).sum=424 := by sorry
