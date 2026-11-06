-- Prove2me | Theorems.Thm_ProbabilityTheory_levySmallJumpPath_ae_eq
-- name    : ProbabilityTheory.levySmallJumpPath_ae_eq
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T12:01:13.313996+00:00
-- url     : https://prove2.me/theorems/0be11df5-13e5-4787-bc58-d6ee94719da4
-- title:
--   LeanLevy: ProbabilityTheory.levySmallJumpPath_ae_eq
-- statement:
--   Source theorem from LeanLevy. The exact theorem type was printed from the pinned compiled Lean environment; the source proof remains to be transplanted and remotely verified.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/RandomMeasure/LevyJumpPath.lean#L1597

import Definitions.Def_LeanLevy_RandomMeasure_LevyJumpLaw
import Definitions.Def_LeanLevy_Processes_Cadlag
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Probability.Martingale.OptionalStopping
import Definitions.Def_LeanLevy_RandomMeasure_LevyJumpPath
open MeasureTheory ProbabilityTheory Filter Set Topology Complex
open scoped NNReal ENNReal BigOperators

theorem ProbabilityTheory.levySmallJumpPath_ae_eq :
  ∀ {Ω : Type} [inst : MeasurableSpace Ω] {K : ℕ → Ω → ℕ} {X : ℕ → ℕ → Ω → ℝ × ℝ} {ν : MeasureTheory.Measure ℝ}
  [inst_1 : MeasureTheory.SigmaFinite ν] {μ : MeasureTheory.Measure Ω} [inst_2 : MeasureTheory.IsProbabilityMeasure μ]
  (hd : ProbabilityTheory.IsPoissonPointFamily K X (MeasureTheory.volume.prod ν) μ)
  (hν : ProbabilityTheory.IsLevyMeasure ν) {t : ℝ},
  0 ≤ t → ProbabilityTheory.levySmallJumpPath hd hν t =ᵐ[μ] ↑↑(ProbabilityTheory.levyCompensatedSmallJump hd hν t) := by sorry
