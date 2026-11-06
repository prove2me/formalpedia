-- Prove2me | Theorems.Thm_ProbabilityTheory_indepFun_partialPieceSum_pieceSum
-- name    : ProbabilityTheory.indepFun_partialPieceSum_pieceSum
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T18:13:47.324713+00:00
-- url     : https://prove2.me/theorems/8b9facdd-b1c8-44dc-8322-84be8fa5a664
-- title:
--   LeanLevy compensated-jump helper: indepFun_partialPieceSum_pieceSum
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

theorem ProbabilityTheory.indepFun_partialPieceSum_pieceSum [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X (volume.prod ν) μ) {f : ℝ × ℝ → ℝ} (hf : Measurable f) (n : ℕ) :
    IndepFun (fun ω => ∑ k ∈ Finset.range (n + 1), pieceSum K X f k ω)
      (pieceSum K X f (n + 1)) μ := by sorry
