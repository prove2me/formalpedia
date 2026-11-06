-- Prove2me | Theorems.Thm_ProbabilityTheory_charFun_map_bandJumpSum
-- name    : ProbabilityTheory.charFun_map_bandJumpSum
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T18:25:15.132582+00:00
-- url     : https://prove2.me/theorems/1c7ac0f8-f209-4459-89d9-0fff5b7dd307
-- title:
--   LeanLevy finite large-jump band helper: charFun_map_bandJumpSum
-- statement:
--   Private original LeanLevy TimeSpacePoisson helper promoted into an owner-private Prove2Me theorem dependency for the Lévy jump characteristic function.

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

theorem ProbabilityTheory.charFun_map_bandJumpSum [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X ((volume : Measure ℝ).prod ν) μ) (hν : IsLevyMeasure ν)
    {s t : ℝ} (hst : s ≤ t) (ξ : ℝ) :
    charFun (μ.map (fun ω => ∑' k,
        pieceSum K X ((Set.Ioc s t ×ˢ {x : ℝ | 1 ≤ |x|}).indicator fun p => p.2) k ω)) ξ
      = Complex.exp (((t - s : ℝ) : ℂ) *
          ∫ x in {x : ℝ | 1 ≤ |x|}, (Complex.exp (x * ξ * Complex.I) - 1) ∂ν) := by sorry
