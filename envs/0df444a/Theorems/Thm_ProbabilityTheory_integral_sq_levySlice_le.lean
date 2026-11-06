-- Prove2me | Theorems.Thm_ProbabilityTheory_integral_sq_levySlice_le
-- name    : ProbabilityTheory.integral_sq_levySlice_le
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T11:48:06.415319+00:00
-- url     : https://prove2.me/theorems/cef7baae-3ebc-4632-915e-b491afa9b248
-- title:
--   LeanLevy: ProbabilityTheory.integral_sq_levySlice_le
-- statement:
--   The `ν`-second moment of the slice is bounded by the geometric tail rate `16⁻ʲ`. The exact theorem type was printed from the pinned compiled Lean environment; the source proof remains to be transplanted and remotely verified.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/RandomMeasure/LevyJumpPath.lean#L917

import Definitions.Def_LeanLevy_RandomMeasure_LevyJumpLaw
import Definitions.Def_LeanLevy_Processes_Cadlag
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Probability.Martingale.OptionalStopping
import Definitions.Def_LeanLevy_RandomMeasure_LevyJumpPath
open MeasureTheory ProbabilityTheory Filter Set Topology Complex
open scoped NNReal ENNReal BigOperators

theorem ProbabilityTheory.integral_sq_levySlice_le :
  ∀ {ν : MeasureTheory.Measure ℝ} (hν : ProbabilityTheory.IsLevyMeasure ν) (j : ℕ),
  ∫ (x : ℝ) in ProbabilityTheory.levySlice hν j, x ^ 2 ∂ν ≤ 16⁻¹ ^ j := by sorry
