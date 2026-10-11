-- Prove2me | Theorems.Thm_PhysMeasureBasis_no_history
-- name    : PhysMeasureBasis.no_history
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T18:55:48.76037+00:00
-- url     : https://prove2.me/theorems/abb18678-3217-4228-b612-98bd7b9b32ee
-- title:
--   `PhysMeasureBasis.no_history` {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℕ → Ω → ℝ) (_hY : ∀ n, Measurable (Y n)) (hlaw : ∀ n, ∀ y : ℝ, P {ω | Y
-- statement:
--   Prove the following Lean 4 theorem from `PhysMeasureBasis`.
--
--   `PhysMeasureBasis.no_history` {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℕ → Ω → ℝ) (_hY : ∀ n, Measurable (Y n)) (hlaw : ∀ n, ∀ y : ℝ, P {ω | Y n ω = y} = 0) (y₀ : ℝ) : P {ω | ∃ n, Y n ω = y₀} = 0
--
--   Formalization note: Lean 4 identifier `PhysMeasureBasis.no_history`.

-- Generated from PhysMeasureBasis.lean — theorem PhysMeasureBasis.no_history
import Mathlib
import Definitions.Def_PhysMeasureBasis
import Definitions.Def_ChapterA4
open PhysMeasureBasis


open MeasureTheory Set ProbabilityTheory
open scoped ENNReal

noncomputable section

theorem PhysMeasureBasis.no_history {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Y : ℕ → Ω → ℝ) (_hY : ∀ n, Measurable (Y n))
    (hlaw : ∀ n, ∀ y : ℝ, P {ω | Y n ω = y} = 0) (y₀ : ℝ) :
    P {ω | ∃ n, Y n ω = y₀} = 0 := by sorry
