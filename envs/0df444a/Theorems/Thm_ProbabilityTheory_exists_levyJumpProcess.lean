-- Prove2me | Theorems.Thm_ProbabilityTheory_exists_levyJumpProcess
-- name    : ProbabilityTheory.exists_levyJumpProcess
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T16:11:06.051376+00:00
-- url     : https://prove2.me/theorems/3f33bdd2-18e6-4ef0-abe7-dd79b653d333
-- title:
--   LeanLevy: ProbabilityTheory.exists_levyJumpProcess
-- statement:
--   Source-header theorem from the pinned LeanLevy library. The source section variables are declared in the preamble. Its original proof has not been transplanted or verified.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/RandomMeasure/LevyJumpLaw.lean#L379

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
import Definitions.Def_LeanLevy_RandomMeasure_LevyJumpLaw
open MeasureTheory Complex ComplexConjugate Set Filter Topology Finset ProbabilityTheory
open scoped NNReal ENNReal
variable {Ω : Type} [MeasurableSpace Ω] {K : ℕ → Ω → ℕ} {X : ℕ → ℕ → Ω → ℝ × ℝ} {ν : Measure ℝ} [SigmaFinite ν] {μ : Measure Ω}

theorem ProbabilityTheory.exists_levyJumpProcess (b : ℝ) {ν : Measure ℝ} (hν : IsLevyMeasure ν) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (X : ℝ≥0 → Ω → ℝ),
      IsProbabilityMeasure μ ∧ HasIndependentIncrements X μ ∧ HasStationaryIncrements X μ ∧
        X 0 =ᵐ[μ] (fun _ => 0) ∧
        ∀ (t : ℝ≥0) (ξ : ℝ), charFun (μ.map (X t)) ξ
          = Complex.exp (((t : ℝ) : ℂ) * (LevyKhintchineTriple.mk b 0 ν hν).exponent ξ) := by sorry
