-- Prove2me | Theorems.Thm_PhysFunctionalAnalysis_polynomial_dense_L2
-- name    : PhysFunctionalAnalysis.polynomial_dense_L2
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T18:51:30.933703+00:00
-- url     : https://prove2.me/theorems/2373004d-78c8-49d6-a37c-64f738f6c89d
-- title:
--   `PhysFunctionalAnalysis.polynomial_dense_L2` : Dense {f : Lp ℝ 2 unitMeasure | ∃ P : Polynomial ℝ, f =ᵐ[unitMeasure] fun x => P.eval x}
-- statement:
--   Prove the following Lean 4 theorem from `PhysFunctionalAnalysis`.
--
--   `PhysFunctionalAnalysis.polynomial_dense_L2` : Dense {f : Lp ℝ 2 unitMeasure | ∃ P : Polynomial ℝ, f =ᵐ[unitMeasure] fun x => P.eval x}
--
--   Formalization note: Lean 4 identifier `PhysFunctionalAnalysis.polynomial_dense_L2`.

-- Generated from PhysFunctionalAnalysis.lean — theorem PhysFunctionalAnalysis.polynomial_dense_L2
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

theorem PhysFunctionalAnalysis.polynomial_dense_L2 :
    Dense {f : Lp ℝ 2 unitMeasure | ∃ P : Polynomial ℝ,
           f =ᵐ[unitMeasure] fun x => P.eval x} := by sorry
