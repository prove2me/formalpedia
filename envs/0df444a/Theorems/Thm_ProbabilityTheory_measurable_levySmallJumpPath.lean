-- Prove2me | Theorems.Thm_ProbabilityTheory_measurable_levySmallJumpPath
-- name    : ProbabilityTheory.measurable_levySmallJumpPath
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T12:02:28.031999+00:00
-- url     : https://prove2.me/theorems/3ad377ef-2422-4f32-bec5-d55f20d83862
-- title:
--   LeanLevy: ProbabilityTheory.measurable_levySmallJumpPath
-- statement:
--   The compensated small-jump path is a measurable function of the sample point at each time: the The exact theorem type was printed from the pinned compiled Lean environment; the source proof remains to be transplanted and remotely verified.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/RandomMeasure/LevyJumpPath.lean#L1420

import Definitions.Def_LeanLevy_RandomMeasure_LevyJumpLaw
import Definitions.Def_LeanLevy_Processes_Cadlag
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Probability.Martingale.OptionalStopping
import Definitions.Def_LeanLevy_RandomMeasure_LevyJumpPath
open MeasureTheory ProbabilityTheory Filter Set Topology Complex
open scoped NNReal ENNReal BigOperators

theorem ProbabilityTheory.measurable_levySmallJumpPath :
  ∀ {Ω : Type} [inst : MeasurableSpace Ω] {K : ℕ → Ω → ℕ} {X : ℕ → ℕ → Ω → ℝ × ℝ} {ν : MeasureTheory.Measure ℝ}
  [inst_1 : MeasureTheory.SigmaFinite ν] {μ : MeasureTheory.Measure Ω}
  (hd : ProbabilityTheory.IsPoissonPointFamily K X (MeasureTheory.volume.prod ν) μ)
  (hν : ProbabilityTheory.IsLevyMeasure ν) (t : ℝ), Measurable (ProbabilityTheory.levySmallJumpPath hd hν t) := by sorry
