-- Prove2me | Theorems.Thm_PhysMeasureBasis_null_singleton
-- name    : PhysMeasureBasis.null_singleton
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T18:52:41.589374+00:00
-- url     : https://prove2.me/theorems/434b036d-b4d6-462a-802a-fc68f771a982
-- title:
--   `PhysMeasureBasis.null_singleton` {α : Type*} [MeasurableSpace α] (μ : Measure α) [MeasurableSingletonClass α] [NullSingletonClass μ] (a : α) : μ {a} = 0
-- statement:
--   Prove the following Lean 4 theorem from `PhysMeasureBasis`.
--
--   `PhysMeasureBasis.null_singleton` {α : Type*} [MeasurableSpace α] (μ : Measure α) [MeasurableSingletonClass α] [NullSingletonClass μ] (a : α) : μ {a} = 0
--
--   Formalization note: Lean 4 identifier `PhysMeasureBasis.null_singleton`.

-- Generated from PhysMeasureBasis.lean — theorem PhysMeasureBasis.null_singleton
import Mathlib
import Definitions.Def_PhysMeasureBasis
import Definitions.Def_ChapterA4
open PhysMeasureBasis


open MeasureTheory Set ProbabilityTheory
open scoped ENNReal

noncomputable section

theorem PhysMeasureBasis.null_singleton {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [MeasurableSingletonClass α] [NullSingletonClass μ] (a : α) : μ {a} = 0 := by sorry
