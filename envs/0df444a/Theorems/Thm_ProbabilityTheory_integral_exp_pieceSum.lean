-- Prove2me | Theorems.Thm_ProbabilityTheory_integral_exp_pieceSum
-- name    : ProbabilityTheory.integral_exp_pieceSum
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T18:13:46.565627+00:00
-- url     : https://prove2.me/theorems/527fe0a7-3056-4cbf-8082-3edfacf44a53
-- title:
--   LeanLevy compensated-jump helper: integral_exp_pieceSum
-- statement:
--   Exact private helper from the original LeanLevy TimeSpacePoisson module, promoted as an owner-private Prove2Me dependency to prove the characteristic function of finite compensated jump sums.

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

theorem ProbabilityTheory.integral_exp_pieceSum [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X (volume.prod ν) μ) {f : ℝ × ℝ → ℝ} (hf : Measurable f) (ξ : ℝ)
    (k : ℕ) :
    ∫ ω, Complex.exp (↑ξ * ↑(pieceSum K X f k ω) * Complex.I) ∂μ
      = Complex.exp (∫ x in prmPiece (volume.prod ν) k,
          (Complex.exp (↑ξ * ↑(f x) * Complex.I) - 1) ∂(volume.prod ν)) := by sorry
