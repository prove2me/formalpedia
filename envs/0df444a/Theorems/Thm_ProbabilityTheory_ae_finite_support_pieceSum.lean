-- Prove2me | Theorems.Thm_ProbabilityTheory_ae_finite_support_pieceSum
-- name    : ProbabilityTheory.ae_finite_support_pieceSum
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T12:21:00.063757+00:00
-- url     : https://prove2.me/theorems/8292e320-83b4-40f3-b03d-b8c9afaf631a
-- title:
--   LeanLevy: ProbabilityTheory.ae_finite_support_pieceSum
-- statement:
--   A.e., the piece sums of a function vanishing off a finite-mass region have finite support. The exact theorem type was printed from the pinned compiled Lean environment; the source proof remains to be transplanted and remotely verified.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/RandomMeasure/TimeSpacePoisson.lean#L392

import Mathlib
import Definitions.Def_LeanLevy_RandomMeasure_TimeSpacePoisson
open MeasureTheory ProbabilityTheory Filter Set Topology Complex
open scoped NNReal ENNReal BigOperators

theorem ProbabilityTheory.ae_finite_support_pieceSum :
  ∀ {Ω : Type} [inst : MeasurableSpace Ω] {ν : MeasureTheory.Measure ℝ} [inst_1 : MeasureTheory.SigmaFinite ν]
  {K : ℕ → Ω → ℕ} {X : ℕ → ℕ → Ω → ℝ × ℝ} {μ : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure μ],
  ProbabilityTheory.IsPoissonPointFamily K X (MeasureTheory.volume.prod ν) μ →
    ∀ {R : Set (ℝ × ℝ)},
      MeasurableSet R →
        (MeasureTheory.volume.prod ν) R < ⊤ →
          ∀ {g : ℝ × ℝ → ℝ}, (∀ p ∉ R, g p = 0) → ∀ᵐ (ω : Ω) ∂μ, {k | ProbabilityTheory.pieceSum K X g k ω ≠ 0}.Finite := by sorry
