-- Prove2me | Theorems.Thm_ProbabilityTheory_convolutionSemigroupOfMeasure_one
-- name    : ProbabilityTheory.convolutionSemigroupOfMeasure_one
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T08:03:08.596166+00:00
-- url     : https://prove2.me/theorems/bc2ecf32-b1cd-474b-b815-b577f3843ea3
-- title:
--   LeanLevy: ProbabilityTheory.convolutionSemigroupOfMeasure_one
-- statement:
--   Source-header theorem from the pinned LeanLevy library. The original mathematical assertion is retained with explicit names and source-compatible universe declarations. Its original proof has not been transplanted or verified.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Levy/LevyKhintchineProof.lean#L5105

import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof

open MeasureTheory MeasureTheory.Measure ProbabilityTheory Complex Filter Topology
open scoped NNReal ENNReal ComplexOrder Real

theorem ProbabilityTheory.convolutionSemigroupOfMeasure_one
    (μ : MeasureTheory.Measure ℝ) [hμ : MeasureTheory.IsProbabilityMeasure μ] (h : IsInfinitelyDivisible μ) :
    ((convolutionSemigroupOfMeasure μ h).measure ⟨1, one_pos⟩ :
        MeasureTheory.ProbabilityMeasure ℝ) = ⟨μ, hμ⟩ := by sorry
