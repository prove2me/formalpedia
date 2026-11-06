-- Prove2me | Theorems.Thm_ProbabilityTheory_charFun_map_compensatedTimeBandSum
-- name    : ProbabilityTheory.charFun_map_compensatedTimeBandSum
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T11:29:45.546657+00:00
-- url     : https://prove2.me/theorems/b47307b8-2f7f-43ee-bc81-1336fc9094e3
-- title:
--   LeanLevy: ProbabilityTheory.charFun_map_compensatedTimeBandSum
-- statement:
--   **Characteristic function of a compensated band sum over `(s, t]`.** For a mark set `A` inside the The exact theorem type was printed from the pinned compiled Lean environment; the source proof remains to be transplanted and remotely verified.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/RandomMeasure/TimeSpacePoisson.lean#L1119

import Mathlib
import Definitions.Def_LeanLevy_RandomMeasure_TimeSpacePoisson
open MeasureTheory ProbabilityTheory Filter Set Topology Complex
open scoped NNReal ENNReal BigOperators

theorem ProbabilityTheory.charFun_map_compensatedTimeBandSum :
  ∀ {Ω : Type} [inst : MeasurableSpace Ω] {ν : MeasureTheory.Measure ℝ} [inst_1 : MeasureTheory.SigmaFinite ν]
  {K : ℕ → Ω → ℕ} {X : ℕ → ℕ → Ω → ℝ × ℝ} {μ : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure μ],
  ProbabilityTheory.IsPoissonPointFamily K X (MeasureTheory.volume.prod ν) μ →
    ∀ {A : Set ℝ},
      MeasurableSet A →
        A ⊆ Set.Ioo (-1) 1 →
          ν A < ⊤ →
            ∀ {s t : ℝ},
              s ≤ t →
                ∀ (ξ : ℝ),
                  MeasureTheory.charFun
                      (MeasureTheory.Measure.map
                        (ProbabilityTheory.compensatedPoissonSum K X ((Set.Ioc s t ×ˢ A).indicator fun p => p.2)
                          (MeasureTheory.volume.prod ν))
                        μ)
                      ξ =
                    Complex.exp
                      (↑(t - s) * ∫ (x : ℝ) in A, Complex.exp (↑x * ↑ξ * Complex.I) - 1 - ↑x * ↑ξ * Complex.I ∂ν) := by sorry
