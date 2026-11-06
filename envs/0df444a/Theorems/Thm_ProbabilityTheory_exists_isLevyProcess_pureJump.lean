-- Prove2me | Theorems.Thm_ProbabilityTheory_exists_isLevyProcess_pureJump
-- name    : ProbabilityTheory.exists_isLevyProcess_pureJump
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T16:52:45.794395+00:00
-- url     : https://prove2.me/theorems/c96c705b-ce68-422d-a3b1-08f358946e6e
-- title:
--   LeanLevy: ProbabilityTheory.exists_isLevyProcess_pureJump
-- statement:
--   Source-header theorem from the pinned LeanLevy library. The source section variables are declared in the preamble. Its original proof has not been transplanted or verified.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/RandomMeasure/LevyJumpPath.lean#L1741

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
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_LeanLevy_RandomMeasure_LevyJumpLaw
import Definitions.Def_LeanLevy_RandomMeasure_LevyJumpPath
open MeasureTheory Complex ComplexConjugate Set Filter Topology Finset ProbabilityTheory
open scoped NNReal ENNReal
variable {Ω : Type} [MeasurableSpace Ω] {K : ℕ → Ω → ℕ}
  {X : ℕ → ℕ → Ω → ℝ × ℝ} {ν : Measure ℝ} [SigmaFinite ν]
  {μ : Measure Ω} {A : Set ℝ}

theorem ProbabilityTheory.exists_isLevyProcess_pureJump (b : ℝ) {ν : Measure ℝ} (hν : IsLevyMeasure ν) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (X : ℝ≥0 → Ω → ℝ),
      IsProbabilityMeasure μ ∧ IsLevyProcess X μ ∧ (∀ t, Measurable (X t)) ∧
      ∀ (t : ℝ≥0) (ξ : ℝ), charFun (μ.map (X t)) ξ =
        Complex.exp (((t : ℝ) : ℂ) * (LevyKhintchineTriple.mk b 0 ν hν).exponent ξ) := by sorry
