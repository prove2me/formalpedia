-- Prove2me | Theorems.Thm_ProbabilityTheory_isLevyProcess_levyJumpPath
-- name    : ProbabilityTheory.isLevyProcess_levyJumpPath
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T11:56:35.193134+00:00
-- url     : https://prove2.me/theorems/702601fd-6896-4243-96aa-a2c29d3c5bee
-- title:
--   LeanLevy: ProbabilityTheory.isLevyProcess_levyJumpPath
-- statement:
--   **The pure-jump process is a genuine Lévy process.** The pathwise `levyJumpPath` realizes the The exact theorem type was printed from the pinned compiled Lean environment; the source proof remains to be transplanted and remotely verified.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/RandomMeasure/LevyJumpPath.lean#L1698

import Definitions.Def_LeanLevy_RandomMeasure_LevyJumpLaw
import Definitions.Def_LeanLevy_Processes_Cadlag
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Probability.Martingale.OptionalStopping
import Definitions.Def_LeanLevy_RandomMeasure_LevyJumpPath
open MeasureTheory ProbabilityTheory Filter Set Topology Complex
open scoped NNReal ENNReal BigOperators

theorem ProbabilityTheory.isLevyProcess_levyJumpPath :
  ∀ {Ω : Type} [inst : MeasurableSpace Ω] {K : ℕ → Ω → ℕ} {X : ℕ → ℕ → Ω → ℝ × ℝ} {ν : MeasureTheory.Measure ℝ}
  [inst_1 : MeasureTheory.SigmaFinite ν] {μ : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure μ]
  (hd : ProbabilityTheory.IsPoissonPointFamily K X (MeasureTheory.volume.prod ν) μ)
  (hν : ProbabilityTheory.IsLevyMeasure ν) (b : ℝ),
  ProbabilityTheory.IsLevyProcess (ProbabilityTheory.levyJumpPath hd hν b) μ := by sorry
