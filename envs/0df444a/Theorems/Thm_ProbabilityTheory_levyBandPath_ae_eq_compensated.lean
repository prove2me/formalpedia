-- Prove2me | Theorems.Thm_ProbabilityTheory_levyBandPath_ae_eq_compensated
-- name    : ProbabilityTheory.levyBandPath_ae_eq_compensated
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T16:57:35.532651+00:00
-- url     : https://prove2.me/theorems/b2a06776-8662-4270-b0a8-c78b7204ad5c
-- title:
--   LeanLevy: ProbabilityTheory.levyBandPath_ae_eq_compensated
-- statement:
--   Source-header theorem from the pinned LeanLevy library. The source section variables are declared in the preamble. Its original proof has not been transplanted or verified.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/RandomMeasure/LevyJumpPath.lean#L268

import Init
import Mathlib.Order.Monotone.Basic
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
variable {Ω : Type} [MeasurableSpace Ω] {K : ℕ → Ω → ℕ}
  {X : ℕ → ℕ → Ω → ℝ × ℝ} {ν : Measure ℝ} [SigmaFinite ν]
  {μ : Measure Ω} {A : Set ℝ}

theorem ProbabilityTheory.levyBandPath_ae_eq_compensated [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X ((volume : Measure ℝ).prod ν) μ)
    (hA : MeasurableSet A) (hAsub : A ⊆ Set.Ioo (-1 : ℝ) 1) (hAfin : ν A < ⊤)
    {t : ℝ} (ht : 0 ≤ t) :
    (fun ω => levyBandPath K X ν A t ω)
      =ᵐ[μ] compensatedPoissonIntegral hd ((memLp_two_bandFun hA hAsub hAfin 0 t).toLp _) := by sorry
