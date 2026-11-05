-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedGlobalTensorHeader_args_cost
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalTensorHeader.args_cost
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T11:33:29.342192+00:00
-- url     : https://prove2.me/theorems/c275a78c-922f-4379-96a0-3f3f1285a215
-- title:
--   args_cost
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/LightTernaryTensorHeader.lean#L38-L39
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/LightTernaryTensorHeader.lean#L38-L39

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryTensorDriverSyntax
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryTensorHeader
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalTensorHeader
open Light LightWeightedGlobalTensorDriver

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalTensorHeader.args_cost : (countArgs.map Expr.cost).sum=424 := by sorry
