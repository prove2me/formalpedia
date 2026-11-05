-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalFastProgramBudget_color_count
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalFastProgramBudget.color_count
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:11:00.525453+00:00
-- url     : https://prove2.me/theorems/0a7ae8e6-87b2-4e17-bc56-6f9e1c3dbcd1
-- title:
--   color_count
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryFastProgramBudget.lean#L16-L19
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryFastProgramBudget.lean#L16-L19

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryFastProgramResources
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryFastProgramBudget
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalFastProgramBudget
open Light StageBounds ArithmeticStageBounds LightColorParametersCosts
open Filter
open scoped Topology

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalFastProgramBudget.color_count : PowerBound (fun n=>ColorParameters.count (width n)) 0 := by sorry
