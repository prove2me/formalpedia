-- Prove2me | Theorems.Thm_ProbabilityTheory_aestronglyMeasurable_levyBandPath_band
-- name    : ProbabilityTheory.aestronglyMeasurable_levyBandPath_band
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T16:22:45.168351+00:00
-- url     : https://prove2.me/theorems/8e03a2b9-d43e-4994-a782-da8517dbe63e
-- title:
--   LeanLevy: ProbabilityTheory.aestronglyMeasurable_levyBandPath_band
-- statement:
--   Source-header theorem from the pinned LeanLevy library. The source section variables are declared in the preamble. Its original proof has not been transplanted or verified.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/RandomMeasure/LevyJumpPath.lean#L346

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
import Definitions.Def_LeanLevy_RandomMeasure_LevyJumpPath
open MeasureTheory Complex ComplexConjugate Set Filter Topology Finset ProbabilityTheory
open scoped NNReal ENNReal
variable {Ω : Type} [MeasurableSpace Ω] {K : ℕ → Ω → ℕ} {X : ℕ → ℕ → Ω → ℝ × ℝ} {ν : Measure ℝ} [SigmaFinite ν] {μ : Measure Ω} {A : Set ℝ}

theorem ProbabilityTheory.aestronglyMeasurable_levyBandPath_band [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X ((volume : Measure ℝ).prod ν) μ)
    (hA : MeasurableSet A) (hAsub : A ⊆ Set.Ioo (-1 : ℝ) 1) (hAfin : ν A < ⊤) (s t : ℝ) :
    AEStronglyMeasurable[prmEvalSigma K X (volume.prod ν) (Set.Ioc s t ×ˢ Set.univ)]
      (compensatedPoissonIntegral hd ((memLp_two_bandFun hA hAsub hAfin s t).toLp _)) μ := by sorry
