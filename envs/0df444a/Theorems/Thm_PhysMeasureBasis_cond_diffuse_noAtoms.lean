-- Prove2me | Theorems.Thm_PhysMeasureBasis_cond_diffuse_noAtoms
-- name    : PhysMeasureBasis.cond_diffuse_noAtoms
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T18:53:24.179436+00:00
-- url     : https://prove2.me/theorems/c673a760-a525-4564-81cf-d0dc4c2f12ac
-- title:
--   `PhysMeasureBasis.cond_diffuse_noAtoms` {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α] (μ : Measure α) [IsFiniteMeasure μ] (_hpos : μ {x | μ {x} ≠ 0}ᶜ ≠ 0) : NullSing
-- statement:
--   Prove the following Lean 4 theorem from `PhysMeasureBasis`.
--
--   `PhysMeasureBasis.cond_diffuse_noAtoms` {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α] (μ : Measure α) [IsFiniteMeasure μ] (_hpos : μ {x | μ {x} ≠ 0}ᶜ ≠ 0) : NullSingletonClass ((μ {x | μ {x} ≠ 0}ᶜ)⁻¹ • μ.restrict {x | μ {x} ≠ 0}ᶜ)
--
--   Formalization note: Lean 4 identifier `PhysMeasureBasis.cond_diffuse_noAtoms`.

-- Generated from PhysMeasureBasis.lean — theorem PhysMeasureBasis.cond_diffuse_noAtoms
import Mathlib
import Definitions.Def_PhysMeasureBasis
import Definitions.Def_ChapterA4
open PhysMeasureBasis


open MeasureTheory Set ProbabilityTheory
open scoped ENNReal

noncomputable section

theorem PhysMeasureBasis.cond_diffuse_noAtoms {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] (μ : Measure α) [IsFiniteMeasure μ]
    (_hpos : μ {x | μ {x} ≠ 0}ᶜ ≠ 0) :
    NullSingletonClass ((μ {x | μ {x} ≠ 0}ᶜ)⁻¹ • μ.restrict {x | μ {x} ≠ 0}ᶜ) := by sorry
