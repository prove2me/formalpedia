-- Prove2me | Theorems.Thm_ProbabilityTheory_isCadlag_levySmallJumpPath
-- name    : ProbabilityTheory.isCadlag_levySmallJumpPath
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T11:51:42.442295+00:00
-- url     : https://prove2.me/theorems/24d0faf5-dae8-4dbe-8330-50852732a9f1
-- title:
--   LeanLevy: ProbabilityTheory.isCadlag_levySmallJumpPath
-- statement:
--   **The compensated small-jump path is càdlàg for every `ω`.** Off the good set the path is The exact theorem type was printed from the pinned compiled Lean environment; the source proof remains to be transplanted and remotely verified.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/RandomMeasure/LevyJumpPath.lean#L1450

import Definitions.Def_LeanLevy_RandomMeasure_LevyJumpLaw
import Definitions.Def_LeanLevy_Processes_Cadlag
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Probability.Martingale.OptionalStopping
import Definitions.Def_LeanLevy_RandomMeasure_LevyJumpPath
open MeasureTheory ProbabilityTheory Filter Set Topology Complex
open scoped NNReal ENNReal BigOperators

theorem ProbabilityTheory.isCadlag_levySmallJumpPath :
  ∀ {Ω : Type} [inst : MeasurableSpace Ω] {K : ℕ → Ω → ℕ} {X : ℕ → ℕ → Ω → ℝ × ℝ} {ν : MeasureTheory.Measure ℝ}
  [inst_1 : MeasureTheory.SigmaFinite ν] {μ : MeasureTheory.Measure Ω}
  (hd : ProbabilityTheory.IsPoissonPointFamily K X (MeasureTheory.volume.prod ν) μ)
  (hν : ProbabilityTheory.IsLevyMeasure ν) (ω : Ω),
  ProbabilityTheory.IsCadlag fun t => ProbabilityTheory.levySmallJumpPath hd hν t ω := by sorry
