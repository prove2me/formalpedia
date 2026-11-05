-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedGlobalTensorDriver_program_main
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalTensorDriver.program_main
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T11:45:15.407765+00:00
-- url     : https://prove2.me/theorems/fc7aa4d0-b114-4f29-8cd8-681b23eb7ef4
-- title:
--   program_main
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/LightTernaryTensorDriver.lean#L44-L48
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/LightTernaryTensorDriver.lean#L44-L48

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryQuarticStep
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryTensorDriver
import Theorems.Thm_ThreeSum_LightTernaryPairedPotential_program_main
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedFrozenQuery_program_main
attribute [local simp] ThreeSum.LightTernaryPairedPotential.program_main


set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalTensorDriver
open Light

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalTensorDriver.program_main (xl yl zl xr yr zr : List ℤ) (K : ℕ) :
    (program xl yl zl xr yr zr K)[entry]?=some (body 142 138 149 147) := by sorry
