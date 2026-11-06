-- Prove2me | Theorems.Thm_ProbabilityTheory_tendsto_setIntegral_annulus
-- name    : ProbabilityTheory.tendsto_setIntegral_annulus
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T18:30:26.293107+00:00
-- url     : https://prove2.me/theorems/ca722617-3c61-47c6-a881-0debece133bd
-- title:
--   LeanLevy small-jump characteristic-function helper: tendsto_setIntegral_annulus
-- statement:
--   Original private LeanLevy TimeSpacePoisson proof helper promoted into owner-private Prove2Me theorem to establish the compensated small-jump characteristic function.

import Definitions.Def_LeanLevy_RandomMeasure_TimeSpacePoisson
import Definitions.Def_LeanLevy_RandomMeasure_PoissonPointFamily
import Definitions.Def_LeanLevy_RandomMeasure_PoissonRandomMeasure
import Definitions.Def_LeanLevy_RandomMeasure_PoissonCompensated
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory ProbabilityTheory Filter Topology Complex
open scoped ENNReal NNReal
variable {Ω : Type} [MeasurableSpace Ω]
  {K : ℕ → Ω → ℕ} {X : ℕ → ℕ → Ω → ℝ × ℝ}
  {ν : Measure ℝ} [SigmaFinite ν] {μ : Measure Ω}

theorem ProbabilityTheory.tendsto_setIntegral_annulus (hν : IsLevyMeasure ν) (ξ : ℝ) :
    Tendsto (fun n : ℕ => ∫ x in Set.Ioo (-1:ℝ) 1 ∩ {x : ℝ | ((n:ℝ) + 1)⁻¹ ≤ |x|},
        (Complex.exp (↑x * ↑ξ * Complex.I) - 1 - ↑x * ↑ξ * Complex.I) ∂ν) atTop
      (𝓝 (∫ x in Set.Ioo (-1:ℝ) 1,
        (Complex.exp (↑x * ↑ξ * Complex.I) - 1 - ↑x * ↑ξ * Complex.I) ∂ν)) := by sorry
