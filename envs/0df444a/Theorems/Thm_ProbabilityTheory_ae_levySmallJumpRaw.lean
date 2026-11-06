-- Prove2me | Theorems.Thm_ProbabilityTheory_ae_levySmallJumpRaw
-- name    : ProbabilityTheory.ae_levySmallJumpRaw
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T11:28:37.320725+00:00
-- url     : https://prove2.me/theorems/b71f866c-33e1-445c-b164-d18cc0ccb0a0
-- title:
--   LeanLevy: ProbabilityTheory.ae_levySmallJumpRaw
-- statement:
--   The raw good event holds almost surely. The exact theorem type was printed from the pinned compiled Lean environment; the source proof remains to be transplanted and remotely verified.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/RandomMeasure/LevyJumpPath.lean#L1029

import Definitions.Def_LeanLevy_RandomMeasure_LevyJumpLaw
import Definitions.Def_LeanLevy_Processes_Cadlag
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Probability.Martingale.OptionalStopping
import Definitions.Def_LeanLevy_RandomMeasure_LevyJumpPath
open MeasureTheory ProbabilityTheory Filter Set Topology Complex
open scoped NNReal ENNReal BigOperators

theorem ProbabilityTheory.ae_levySmallJumpRaw :
  ∀ {Ω : Type} [inst : MeasurableSpace Ω] {K : ℕ → Ω → ℕ} {X : ℕ → ℕ → Ω → ℝ × ℝ} {ν : MeasureTheory.Measure ℝ}
  [inst_1 : MeasureTheory.SigmaFinite ν] {μ : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure μ]
  (hd : ProbabilityTheory.IsPoissonPointFamily K X (MeasureTheory.volume.prod ν) μ)
  (hν : ProbabilityTheory.IsLevyMeasure ν), ∀ᵐ (ω : Ω) ∂μ, ProbabilityTheory.levySmallJumpRaw hd hν ω := by sorry
