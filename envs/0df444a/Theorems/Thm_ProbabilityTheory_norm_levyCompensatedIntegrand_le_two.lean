-- Prove2me | Theorems.Thm_ProbabilityTheory_norm_levyCompensatedIntegrand_le_two
-- name    : ProbabilityTheory.norm_levyCompensatedIntegrand_le_two
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T15:12:45.652658+00:00
-- url     : https://prove2.me/theorems/6647ed9d-0394-4a32-bee8-de73f0747c32
-- title:
--   LeanLevy: ProbabilityTheory.norm_levyCompensatedIntegrand_le_two
-- statement:
--   Source-header theorem from the pinned LeanLevy library. The source section parameters are made explicit. Its original proof has not been transplanted or verified.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Levy/CompensatedIntegral.lean#L85

import Mathlib
import Definitions.Def_LeanLevy_Levy_CompensatedIntegral
open MeasureTheory Complex ComplexConjugate Set Filter Topology Finset ProbabilityTheory
open scoped NNReal ENNReal

theorem ProbabilityTheory.norm_levyCompensatedIntegrand_le_two {ξ x : ℝ} (hx : 1 ≤ |x|) :
    ‖levyCompensatedIntegrand ξ x‖ ≤ 2 := by sorry
