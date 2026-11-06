-- Prove2me | Theorems.Thm_ProbabilityTheory_charFun_partial_compensatedBandSum
-- name    : ProbabilityTheory.charFun_partial_compensatedBandSum
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T18:13:46.85848+00:00
-- url     : https://prove2.me/theorems/3686360d-8916-49f5-92d2-178786a07941
-- title:
--   LeanLevy compensated-jump helper: charFun_partial_compensatedBandSum
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

theorem ProbabilityTheory.charFun_partial_compensatedBandSum [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X (volume.prod ν) μ) {f : ℝ × ℝ → ℝ} (hf : Measurable f)
    (hf1 : Integrable f (volume.prod ν)) (ξ : ℝ) (n : ℕ) :
    ∫ ω, Complex.exp (↑ξ * ↑(∑ k ∈ Finset.range (n + 1),
        compensatedPieceSum K X f (volume.prod ν) k ω) * Complex.I) ∂μ
      = ∏ k ∈ Finset.range (n + 1),
          Complex.exp (∫ x in prmPiece (volume.prod ν) k,
            (Complex.exp (↑ξ * ↑(f x) * Complex.I) - 1 - ↑ξ * ↑(f x) * Complex.I)
              ∂(volume.prod ν)) := by sorry
