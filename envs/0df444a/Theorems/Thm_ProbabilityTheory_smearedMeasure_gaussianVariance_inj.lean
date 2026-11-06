-- Prove2me | Theorems.Thm_ProbabilityTheory_smearedMeasure_gaussianVariance_inj
-- name    : ProbabilityTheory.smearedMeasure_gaussianVariance_inj
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T16:02:14.57627+00:00
-- url     : https://prove2.me/theorems/8cc210e4-7a5e-4829-8eaa-9b42b0191211
-- title:
--   LeanLevy: ProbabilityTheory.smearedMeasure_gaussianVariance_inj
-- statement:
--   Source-header theorem from the pinned LeanLevy library. The source section variables are declared in the preamble. Its original proof has not been transplanted or verified.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Levy/LevyKhintchineUniqueness.lean#L458

import Init
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Data.Complex.Basic
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Definitions.Def_LeanLevy_Levy_CharacteristicExponent
import Definitions.Def_LeanLevy_Levy_LevyKhintchine
import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof
import Definitions.Def_LeanLevy_Levy_LevyKhintchineUniqueness
open MeasureTheory Complex ComplexConjugate Set Filter Topology Finset ProbabilityTheory
open scoped NNReal ENNReal

theorem ProbabilityTheory.smearedMeasure_gaussianVariance_inj {ν₁ ν₂ : Measure ℝ}
    (hν₁ : IsLevyMeasure ν₁) (hν₂ : IsLevyMeasure ν₂) {σ₁ σ₂ : ℝ≥0}
    (h : smearedMeasure σ₁ ν₁ = smearedMeasure σ₂ ν₂) : σ₁ = σ₂ := by sorry
