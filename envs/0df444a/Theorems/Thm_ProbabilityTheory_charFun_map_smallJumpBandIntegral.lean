-- Prove2me | Theorems.Thm_ProbabilityTheory_charFun_map_smallJumpBandIntegral
-- name    : ProbabilityTheory.charFun_map_smallJumpBandIntegral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T18:30:22.589864+00:00
-- url     : https://prove2.me/theorems/c711a1eb-c990-4869-93be-e545d584333e
-- title:
--   LeanLevy small-jump characteristic-function helper: charFun_map_smallJumpBandIntegral
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

theorem ProbabilityTheory.charFun_map_smallJumpBandIntegral [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X ((volume : Measure ℝ).prod ν) μ) (hν : IsLevyMeasure ν)
    {s t : ℝ} (hst : s ≤ t) (ξ : ℝ) :
    charFun (μ.map (fun ω => (compensatedPoissonIntegral hd
        ((memLp_two_smallJumpBandFun hν s t).toLp
          ((Set.Ioc s t ×ˢ Set.Ioo (-1:ℝ) 1).indicator fun p => p.2))) ω)) ξ
      = Complex.exp (((t - s : ℝ) : ℂ) * ∫ x in Set.Ioo (-1) 1,
          (Complex.exp (x * ξ * Complex.I) - 1 - x * ξ * Complex.I) ∂ν) := by sorry
