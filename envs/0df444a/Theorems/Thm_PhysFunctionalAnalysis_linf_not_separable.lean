-- Prove2me | Theorems.Thm_PhysFunctionalAnalysis_linf_not_separable
-- name    : PhysFunctionalAnalysis.linf_not_separable
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T18:51:18.386018+00:00
-- url     : https://prove2.me/theorems/088cd898-530a-4c44-8c39-5b7b546e36df
-- title:
--   `PhysFunctionalAnalysis.linf_not_separable` : ¬ TopologicalSpace.SeparableSpace (Lp ℝ ⊤ unitMeasure)
-- statement:
--   Prove the following Lean 4 theorem from `PhysFunctionalAnalysis`.
--
--   `PhysFunctionalAnalysis.linf_not_separable` : ¬ TopologicalSpace.SeparableSpace (Lp ℝ ⊤ unitMeasure)
--
--   Formalization note: Lean 4 identifier `PhysFunctionalAnalysis.linf_not_separable`.

-- Generated from PhysFunctionalAnalysis.lean — theorem PhysFunctionalAnalysis.linf_not_separable
import Mathlib
import Definitions.Def_PhysFunctionalAnalysis
import Definitions.Def_PhysMeasureBasis
import Definitions.Def_ChapterA4
open PhysMeasureBasis
open PhysFunctionalAnalysis


open MeasureTheory Set
open scoped ENNReal lp

noncomputable section


open PhysMeasureBasis

theorem PhysFunctionalAnalysis.linf_not_separable :
    ¬ TopologicalSpace.SeparableSpace (Lp ℝ ⊤ unitMeasure) := by sorry
