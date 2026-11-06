-- Prove2me | Theorems.Thm_ProbabilityTheory_charFun_map_levyJumpPath
-- name    : ProbabilityTheory.charFun_map_levyJumpPath
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T16:51:09.2081+00:00
-- url     : https://prove2.me/theorems/621efc54-4815-4df3-8dd2-956df9b6e2c0
-- title:
--   LeanLevy: ProbabilityTheory.charFun_map_levyJumpPath
-- statement:
--   Source-header theorem from the pinned LeanLevy library. The source section variables are declared in the preamble. Its original proof has not been transplanted or verified.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/RandomMeasure/LevyJumpPath.lean#L1731

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

theorem ProbabilityTheory.charFun_map_levyJumpPath [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X ((volume : Measure ℝ).prod ν) μ) (hν : IsLevyMeasure ν)
    (b : ℝ) (t : ℝ≥0) (ξ : ℝ) :
    charFun (μ.map (levyJumpPath hd hν b t)) ξ
      = Complex.exp (((t : ℝ) : ℂ) * (LevyKhintchineTriple.mk b 0 ν hν).exponent ξ) := by sorry
