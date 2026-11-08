-- Prove2me | Theorems.Thm_ProbabilityTheory_convolutionSemigroupOfMeasure_one_coe
-- name    : ProbabilityTheory.convolutionSemigroupOfMeasure_one_coe
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T08:03:28.820744+00:00
-- url     : https://prove2.me/theorems/6ffb783d-5a22-4a7c-b0c0-4e6e57dbc7bf
-- title:
--   LeanLevy: ProbabilityTheory.convolutionSemigroupOfMeasure_one_coe
-- statement:
--   Source-header theorem from the pinned LeanLevy library. The original mathematical assertion is retained with explicit names and source-compatible universe declarations. Its original proof has not been transplanted or verified.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Levy/LevyKhintchineProof.lean#L5115

import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof

open MeasureTheory MeasureTheory.Measure ProbabilityTheory Complex Filter Topology
open scoped NNReal ENNReal ComplexOrder Real

theorem ProbabilityTheory.convolutionSemigroupOfMeasure_one_coe
    (μ : MeasureTheory.Measure ℝ) [hμ : MeasureTheory.IsProbabilityMeasure μ] (h : IsInfinitelyDivisible μ) :
    (((convolutionSemigroupOfMeasure μ h).measure ⟨1, one_pos⟩ :
        MeasureTheory.ProbabilityMeasure ℝ) : MeasureTheory.Measure ℝ) = μ := by sorry
