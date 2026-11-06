-- Prove2me | Theorems.Thm_ProbabilityTheory_integral_compensatedPoissonIntegral
-- name    : ProbabilityTheory.integral_compensatedPoissonIntegral
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T12:30:44.442325+00:00
-- url     : https://prove2.me/theorems/6655a1fe-ed9d-405f-b20a-d3de77587967
-- title:
--   LeanLevy: ProbabilityTheory.integral_compensatedPoissonIntegral
-- statement:
--   The compensated Poisson integral of any `L²` function has mean zero. The exact theorem type was printed from the pinned compiled Lean environment; the source proof remains to be transplanted and remotely verified.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/RandomMeasure/PoissonCompensated.lean#L817

import Mathlib
import Definitions.Def_LeanLevy_RandomMeasure_PoissonCompensated
open MeasureTheory ProbabilityTheory Filter Set Topology Complex
open scoped NNReal ENNReal BigOperators

theorem ProbabilityTheory.integral_compensatedPoissonIntegral :
  ∀ {Ω E : Type} [inst : MeasurableSpace E] [inst_1 : MeasurableSpace Ω] {K : ℕ → Ω → ℕ}
    {X : ℕ → ℕ → Ω → E} {m : MeasureTheory.Measure E} [inst_2 : MeasureTheory.SigmaFinite m]
    [inst_3 : Nonempty E] {μ : MeasureTheory.Measure Ω} [inst_4 : MeasureTheory.IsProbabilityMeasure μ]
    (hd : ProbabilityTheory.IsPoissonPointFamily K X m μ) (f : MeasureTheory.Lp ℝ 2 m),
  ∫ (ω : Ω), ProbabilityTheory.compensatedPoissonIntegral hd f ω ∂μ = 0 := by sorry
