-- Prove2me | Theorems.Thm_PhysMeasureBasis_selection_exists
-- name    : PhysMeasureBasis.selection_exists
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T18:52:41.357671+00:00
-- url     : https://prove2.me/theorems/c23c5a06-5cef-40cf-a3e4-e13a6d6fd703
-- title:
--   `PhysMeasureBasis.selection_exists` : squareMeasure.fst ⊗ₘ squareMeasure.condKernel = squareMeasure
-- statement:
--   Prove the following Lean 4 theorem from `PhysMeasureBasis`.
--
--   `PhysMeasureBasis.selection_exists` : squareMeasure.fst ⊗ₘ squareMeasure.condKernel = squareMeasure
--
--   Formalization note: Lean 4 identifier `PhysMeasureBasis.selection_exists`.

-- Generated from PhysMeasureBasis.lean — theorem PhysMeasureBasis.selection_exists
import Mathlib
import Definitions.Def_PhysMeasureBasis
import Definitions.Def_ChapterA4
open PhysMeasureBasis


open MeasureTheory Set ProbabilityTheory
open scoped ENNReal

noncomputable section

theorem PhysMeasureBasis.selection_exists :
    squareMeasure.fst ⊗ₘ squareMeasure.condKernel = squareMeasure := by sorry
