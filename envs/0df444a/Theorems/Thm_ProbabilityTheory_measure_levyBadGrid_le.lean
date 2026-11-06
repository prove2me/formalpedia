-- Prove2me | Theorems.Thm_ProbabilityTheory_measure_levyBadGrid_le
-- name    : ProbabilityTheory.measure_levyBadGrid_le
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T12:06:26.869971+00:00
-- url     : https://prove2.me/theorems/c56b2c9b-1863-43f6-8c9d-99fdc471710d
-- title:
--   LeanLevy: ProbabilityTheory.measure_levyBadGrid_le
-- statement:
--   Task-4 maximal inequality applied to the slice path: the bad-grid event has measure at most The exact theorem type was printed from the pinned compiled Lean environment; the source proof remains to be transplanted and remotely verified.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/RandomMeasure/LevyJumpPath.lean#L965

import Definitions.Def_LeanLevy_RandomMeasure_LevyJumpLaw
import Definitions.Def_LeanLevy_Processes_Cadlag
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Probability.Martingale.OptionalStopping
import Definitions.Def_LeanLevy_RandomMeasure_LevyJumpPath
open MeasureTheory ProbabilityTheory Filter Set Topology Complex
open scoped NNReal ENNReal BigOperators

theorem ProbabilityTheory.measure_levyBadGrid_le :
  ∀ {Ω : Type} [inst : MeasurableSpace Ω] {K : ℕ → Ω → ℕ} {X : ℕ → ℕ → Ω → ℝ × ℝ} {ν : MeasureTheory.Measure ℝ}
  [inst_1 : MeasureTheory.SigmaFinite ν] {μ : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure μ]
  (hd : ProbabilityTheory.IsPoissonPointFamily K X (MeasureTheory.volume.prod ν) μ)
  (hν : ProbabilityTheory.IsLevyMeasure ν) (T j : ℕ),
  μ (ProbabilityTheory.levyBadGrid hd hν T j) ≤ ENNReal.ofReal (√↑T * 2⁻¹ ^ j) := by sorry
