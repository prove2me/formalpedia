-- Prove2me | Theorems.Thm_ProbabilityTheory_levyCompensatedIntegrand_zero_left
-- name    : ProbabilityTheory.levyCompensatedIntegrand_zero_left
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T15:12:29.346378+00:00
-- url     : https://prove2.me/theorems/7ab3a6c0-c661-4c77-b52c-73681b3defe0
-- title:
--   LeanLevy: ProbabilityTheory.levyCompensatedIntegrand_zero_left
-- statement:
--   Source-header theorem from the pinned LeanLevy library. The source section parameters are made explicit. Its original proof has not been transplanted or verified.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Levy/CompensatedIntegral.lean#L53

import Mathlib
import Definitions.Def_LeanLevy_Levy_CompensatedIntegral
open MeasureTheory Complex ComplexConjugate Set Filter Topology Finset ProbabilityTheory
open scoped NNReal ENNReal

theorem ProbabilityTheory.levyCompensatedIntegrand_zero_left (x : ℝ) :
    levyCompensatedIntegrand 0 x = 0 := by sorry
