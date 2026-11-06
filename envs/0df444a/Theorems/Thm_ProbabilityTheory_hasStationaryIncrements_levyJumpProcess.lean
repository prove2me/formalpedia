-- Prove2me | Theorems.Thm_ProbabilityTheory_hasStationaryIncrements_levyJumpProcess
-- name    : ProbabilityTheory.hasStationaryIncrements_levyJumpProcess
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T11:44:05.038327+00:00
-- url     : https://prove2.me/theorems/a36f9736-aae4-4ac4-b51e-b8920f9f7cec
-- title:
--   LeanLevy: ProbabilityTheory.hasStationaryIncrements_levyJumpProcess
-- statement:
--   **Stationary increments of the jump process.** The law of the increment over `(s, s + h]` The exact theorem type was printed from the pinned compiled Lean environment; the source proof remains to be transplanted and remotely verified.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/RandomMeasure/LevyJumpLaw.lean#L344

import Definitions.Def_LeanLevy_RandomMeasure_LevyJumpLaw
import Definitions.Def_LeanLevy_RandomMeasure_PoissonMartingale
import Definitions.Def_LeanLevy_Levy_LevyKhintchineUniqueness
open MeasureTheory ProbabilityTheory Complex
open scoped ENNReal NNReal

theorem ProbabilityTheory.hasStationaryIncrements_levyJumpProcess :
  ∀ {Ω : Type} [inst : MeasurableSpace Ω] {K : ℕ → Ω → ℕ} {X : ℕ → ℕ → Ω → ℝ × ℝ} {ν : MeasureTheory.Measure ℝ}
  [inst_1 : MeasureTheory.SigmaFinite ν] {μ : MeasureTheory.Measure Ω} [inst_2 : MeasureTheory.IsProbabilityMeasure μ]
  (hd : ProbabilityTheory.IsPoissonPointFamily K X (MeasureTheory.volume.prod ν) μ)
  (hν : ProbabilityTheory.IsLevyMeasure ν) (b : ℝ),
  ProbabilityTheory.HasStationaryIncrements (ProbabilityTheory.levyJumpProcess hd hν b) μ := by sorry
