-- Prove2me | Theorems.Thm_ProbabilityTheory_levyJumpPath_zero
-- name    : ProbabilityTheory.levyJumpPath_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T16:46:19.519497+00:00
-- url     : https://prove2.me/theorems/68502908-e0bb-48b9-9b73-be93d991145c
-- title:
--   LeanLevy: ProbabilityTheory.levyJumpPath_zero
-- statement:
--   Source-header theorem from the pinned LeanLevy library. The source section variables are declared in the preamble. Its original proof has not been transplanted or verified.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/RandomMeasure/LevyJumpPath.lean#L1646

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

theorem ProbabilityTheory.levyJumpPath_zero
    (hd : IsPoissonPointFamily K X ((volume : Measure ℝ).prod ν) μ) (hν : IsLevyMeasure ν) (b : ℝ) :
    levyJumpPath hd hν b 0 = fun _ => 0 := by sorry
