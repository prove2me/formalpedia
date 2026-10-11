-- Prove2me | Theorems.Thm_PhysMeasureBasis_atomless_mutuallySingular_atomic
-- name    : PhysMeasureBasis.atomless_mutuallySingular_atomic
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T18:54:46.855595+00:00
-- url     : https://prove2.me/theorems/a8a0b35e-529d-4325-bc89-3fe77441d181
-- title:
--   `PhysMeasureBasis.atomless_mutuallySingular_atomic` {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α] (μ ν : Measure α) [NullSingletonClass μ] {A : Set α} (hA : A.Counta
-- statement:
--   Prove the following Lean 4 theorem from `PhysMeasureBasis`.
--
--   `PhysMeasureBasis.atomless_mutuallySingular_atomic` {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α] (μ ν : Measure α) [NullSingletonClass μ] {A : Set α} (hA : A.Countable) (hν : ν Aᶜ = 0) : μ ⟂ₘ ν
--
--   Formalization note: Lean 4 identifier `PhysMeasureBasis.atomless_mutuallySingular_atomic`.

-- Generated from PhysMeasureBasis.lean — theorem PhysMeasureBasis.atomless_mutuallySingular_atomic
import Mathlib
import Definitions.Def_PhysMeasureBasis
import Definitions.Def_ChapterA4
open PhysMeasureBasis


open MeasureTheory Set ProbabilityTheory
open scoped ENNReal

noncomputable section

theorem PhysMeasureBasis.atomless_mutuallySingular_atomic {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] (μ ν : Measure α) [NullSingletonClass μ]
    {A : Set α} (hA : A.Countable) (hν : ν Aᶜ = 0) :
    μ ⟂ₘ ν := by sorry
