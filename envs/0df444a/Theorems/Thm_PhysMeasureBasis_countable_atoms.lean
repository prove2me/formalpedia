-- Prove2me | Theorems.Thm_PhysMeasureBasis_countable_atoms
-- name    : PhysMeasureBasis.countable_atoms
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T18:52:53.933985+00:00
-- url     : https://prove2.me/theorems/66f0a5be-2ef5-4302-97a3-a0419dbc7673
-- title:
--   `PhysMeasureBasis.countable_atoms` {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α] (μ : Measure α) [IsFiniteMeasure μ] : {x | μ {x} ≠ 0}.Countable
-- statement:
--   Prove the following Lean 4 theorem from `PhysMeasureBasis`.
--
--   `PhysMeasureBasis.countable_atoms` {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α] (μ : Measure α) [IsFiniteMeasure μ] : {x | μ {x} ≠ 0}.Countable
--
--   Formalization note: Lean 4 identifier `PhysMeasureBasis.countable_atoms`.

-- Generated from PhysMeasureBasis.lean — theorem PhysMeasureBasis.countable_atoms
import Mathlib
import Definitions.Def_PhysMeasureBasis
import Definitions.Def_ChapterA4
open PhysMeasureBasis


open MeasureTheory Set ProbabilityTheory
open scoped ENNReal

noncomputable section

theorem PhysMeasureBasis.countable_atoms {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] (μ : Measure α) [IsFiniteMeasure μ] :
    {x | μ {x} ≠ 0}.Countable := by sorry
