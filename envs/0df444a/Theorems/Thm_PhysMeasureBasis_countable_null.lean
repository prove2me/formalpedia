-- Prove2me | Theorems.Thm_PhysMeasureBasis_countable_null
-- name    : PhysMeasureBasis.countable_null
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T18:52:33.160179+00:00
-- url     : https://prove2.me/theorems/e41a3d8f-18b2-4996-80da-92c18e3a8e30
-- title:
--   `PhysMeasureBasis.countable_null` {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α] (μ : Measure α) [NullSingletonClass μ] {s : Set α} (hs : s.Countable) : μ s = 0
-- statement:
--   Prove the following Lean 4 theorem from `PhysMeasureBasis`.
--
--   `PhysMeasureBasis.countable_null` {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α] (μ : Measure α) [NullSingletonClass μ] {s : Set α} (hs : s.Countable) : μ s = 0
--
--   Formalization note: Lean 4 identifier `PhysMeasureBasis.countable_null`.

-- Generated from PhysMeasureBasis.lean — theorem PhysMeasureBasis.countable_null
import Mathlib
import Definitions.Def_PhysMeasureBasis
import Definitions.Def_ChapterA4
open PhysMeasureBasis


open MeasureTheory Set ProbabilityTheory
open scoped ENNReal

noncomputable section

theorem PhysMeasureBasis.countable_null {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] (μ : Measure α) [NullSingletonClass μ]
    {s : Set α} (hs : s.Countable) : μ s = 0 := by sorry
