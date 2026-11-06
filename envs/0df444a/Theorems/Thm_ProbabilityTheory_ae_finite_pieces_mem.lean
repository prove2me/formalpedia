-- Prove2me | Theorems.Thm_ProbabilityTheory_ae_finite_pieces_mem
-- name    : ProbabilityTheory.ae_finite_pieces_mem
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T11:26:36.751586+00:00
-- url     : https://prove2.me/theorems/347ee317-d493-4173-b368-e99cc1f07802
-- title:
--   LeanLevy: ProbabilityTheory.ae_finite_pieces_mem
-- statement:
--   A.e., only finitely many pieces carry a realized point in a finite-mass region. The exact theorem type was printed from the pinned compiled Lean environment; the source proof remains to be transplanted and remotely verified.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/RandomMeasure/TimeSpacePoisson.lean#L367

import Mathlib
import Definitions.Def_LeanLevy_RandomMeasure_TimeSpacePoisson
open MeasureTheory ProbabilityTheory Filter Set Topology Complex
open scoped NNReal ENNReal BigOperators

theorem ProbabilityTheory.ae_finite_pieces_mem :
  ∀ {Ω : Type} [inst : MeasurableSpace Ω] {ν : MeasureTheory.Measure ℝ} [inst_1 : MeasureTheory.SigmaFinite ν]
  {K : ℕ → Ω → ℕ} {X : ℕ → ℕ → Ω → ℝ × ℝ} {μ : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure μ],
  ProbabilityTheory.IsPoissonPointFamily K X (MeasureTheory.volume.prod ν) μ →
    ∀ {R : Set (ℝ × ℝ)},
      MeasurableSet R →
        (MeasureTheory.volume.prod ν) R < ⊤ → ∀ᵐ (ω : Ω) ∂μ, {k | ∃ n ∈ Finset.range (K k ω), X k n ω ∈ R}.Finite := by sorry
