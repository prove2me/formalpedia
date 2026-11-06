-- Prove2me | Theorems.Thm_ProbabilityTheory_measure_countable_sup_levyBandPath_ge
-- name    : ProbabilityTheory.measure_countable_sup_levyBandPath_ge
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T12:04:46.932733+00:00
-- url     : https://prove2.me/theorems/e49c9ac1-f10d-4578-9136-a81101f3dafb
-- title:
--   LeanLevy: ProbabilityTheory.measure_countable_sup_levyBandPath_ge
-- statement:
--   **Maximal inequality over a countable grid.** For a band `A ⊆ (-1, 1)` of finite `ν`-mass and a The exact theorem type was printed from the pinned compiled Lean environment; the source proof remains to be transplanted and remotely verified.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/RandomMeasure/LevyJumpPath.lean#L674

import Definitions.Def_LeanLevy_RandomMeasure_LevyJumpLaw
import Definitions.Def_LeanLevy_Processes_Cadlag
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Probability.Martingale.OptionalStopping
import Definitions.Def_LeanLevy_RandomMeasure_LevyJumpPath
open MeasureTheory ProbabilityTheory Filter Set Topology Complex
open scoped NNReal ENNReal BigOperators

theorem ProbabilityTheory.measure_countable_sup_levyBandPath_ge :
  ∀ {Ω : Type} [inst : MeasurableSpace Ω] {K : ℕ → Ω → ℕ} {X : ℕ → ℕ → Ω → ℝ × ℝ} {ν : MeasureTheory.Measure ℝ}
  [inst_1 : MeasureTheory.SigmaFinite ν] {μ : MeasureTheory.Measure Ω} {A : Set ℝ}
  [MeasureTheory.IsProbabilityMeasure μ],
  ProbabilityTheory.IsPoissonPointFamily K X (MeasureTheory.volume.prod ν) μ →
    ProbabilityTheory.IsLevyMeasure ν →
      MeasurableSet A →
        A ⊆ Set.Ioo (-1) 1 →
          ν A < ⊤ →
            ∀ {T : ℝ},
              0 ≤ T →
                ∀ {D : Set ℝ},
                  D.Countable →
                    D ⊆ Set.Icc 0 T →
                      ∀ {ε : NNReal},
                        0 < ε →
                          μ {ω | ∃ t ∈ D, ↑ε ≤ |ProbabilityTheory.levyBandPath K X ν A t ω|} ≤
                            ENNReal.ofReal √(T * ∫ (x : ℝ) in A, x ^ 2 ∂ν) / ↑ε := by sorry
