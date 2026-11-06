-- Prove2me | Theorems.Thm_ProbabilityTheory_charFun_map_levyJumpProcess
-- name    : ProbabilityTheory.charFun_map_levyJumpProcess
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T12:27:27.339984+00:00
-- url     : https://prove2.me/theorems/5b5fc91f-108c-4886-921a-94e89352692c
-- title:
--   LeanLevy: ProbabilityTheory.charFun_map_levyJumpProcess
-- statement:
--   The marginal law of the jump process at time `t`. The exact theorem type was printed from the pinned compiled Lean environment; the source proof remains to be transplanted and remotely verified.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/RandomMeasure/LevyJumpLaw.lean#L326

import Definitions.Def_LeanLevy_RandomMeasure_LevyJumpLaw
import Definitions.Def_LeanLevy_RandomMeasure_PoissonMartingale
import Definitions.Def_LeanLevy_Levy_LevyKhintchineUniqueness
open MeasureTheory ProbabilityTheory Complex
open scoped ENNReal NNReal

theorem ProbabilityTheory.charFun_map_levyJumpProcess :
  ∀ {Ω : Type} [inst : MeasurableSpace Ω] {K : ℕ → Ω → ℕ} {X : ℕ → ℕ → Ω → ℝ × ℝ} {ν : MeasureTheory.Measure ℝ}
  [inst_1 : MeasureTheory.SigmaFinite ν] {μ : MeasureTheory.Measure Ω} [inst_2 : MeasureTheory.IsProbabilityMeasure μ]
  (hd : ProbabilityTheory.IsPoissonPointFamily K X (MeasureTheory.volume.prod ν) μ)
  (hν : ProbabilityTheory.IsLevyMeasure ν) (b : ℝ) (t : NNReal) (ξ : ℝ),
  MeasureTheory.charFun (MeasureTheory.Measure.map (ProbabilityTheory.levyJumpProcess hd hν b t) μ) ξ =
    Complex.exp (((t : ℝ) : ℂ) * (ProbabilityTheory.LevyKhintchineTriple.mk b 0 ν hν).exponent ξ) := by sorry
