-- Prove2me | Theorems.Thm_ProbabilityTheory_measurable_levyCompensatedIntegrand
-- name    : ProbabilityTheory.measurable_levyCompensatedIntegrand
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T22:16:00.376112+00:00
-- url     : https://prove2.me/theorems/5450311b-fc56-43d8-ac7d-13972de90505
-- title:
--   LeanLevy: ProbabilityTheory.measurable_levyCompensatedIntegrand
-- statement:
--   The compensated integrand is measurable in `x` for fixed `ξ`. Exact extracted Lean theorem type; proof pending Prove2Me verification.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4//home/willr/projects/Prove2Me/scratch/leanlevy_bulk_20261027/source/LeanLevy/Levy/CompensatedIntegral.lean#L73

import Definitions.Def_LeanLevy_Levy_CompensatedIntegral
import Definitions.Def_LeanLevy_Levy_LevyMeasure
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set

theorem ProbabilityTheory.measurable_levyCompensatedIntegrand : ∀ (ξ : Real),
  @Measurable Real Complex Real.measurableSpace Complex.measurableSpace (ProbabilityTheory.levyCompensatedIntegrand ξ) := by sorry
