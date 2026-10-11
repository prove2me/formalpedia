-- Prove2me | Theorems.Thm_PhysFunctionalAnalysis_countable_of_separated
-- name    : PhysFunctionalAnalysis.countable_of_separated
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T18:52:54.072426+00:00
-- url     : https://prove2.me/theorems/72f41cf8-3741-47e9-888b-857224b44917
-- title:
--   `PhysFunctionalAnalysis.countable_of_separated` {X : Type*} [PseudoMetricSpace X] [TopologicalSpace.SeparableSpace X] {ι : Type*} (u : ι → X) {r : ℝ} (hr : 0 < r) (hsep : ∀ i j, i
-- statement:
--   Prove the following Lean 4 theorem from `PhysFunctionalAnalysis`.
--
--   `PhysFunctionalAnalysis.countable_of_separated` {X : Type*} [PseudoMetricSpace X] [TopologicalSpace.SeparableSpace X] {ι : Type*} (u : ι → X) {r : ℝ} (hr : 0 < r) (hsep : ∀ i j, i ≠ j → r ≤ dist (u i) (u j)) : Countable ι
--
--   Formalization note: Lean 4 identifier `PhysFunctionalAnalysis.countable_of_separated`.

-- Generated from PhysFunctionalAnalysis.lean — theorem PhysFunctionalAnalysis.countable_of_separated
import Mathlib
import Definitions.Def_PhysFunctionalAnalysis
import Definitions.Def_ChapterA4
open PhysFunctionalAnalysis


open MeasureTheory Set
open scoped ENNReal lp

noncomputable section


open PhysMeasureBasis

theorem PhysFunctionalAnalysis.countable_of_separated {X : Type*} [PseudoMetricSpace X]
    [TopologicalSpace.SeparableSpace X] {ι : Type*} (u : ι → X) {r : ℝ} (hr : 0 < r)
    (hsep : ∀ i j, i ≠ j → r ≤ dist (u i) (u j)) : Countable ι := by sorry
