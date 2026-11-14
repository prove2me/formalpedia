-- Prove2me | Theorems.Thm_ProbabilityTheory_IsLevyProcess_charFun_marginal_cpow
-- name    : ProbabilityTheory.IsLevyProcess.charFun_marginal_cpow
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T15:11:08.128481+00:00
-- url     : https://prove2.me/theorems/87060483-c5f1-445b-a454-84cf28f77d84
-- title:
--   LeanLevy: ProbabilityTheory.IsLevyProcess.charFun_marginal_cpow
-- statement:
--   Source-header theorem from the pinned LeanLevy library. The source section parameters are made explicit. Its original proof has not been transplanted or verified.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Levy/CharacteristicExponent.lean#L467

import Init
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Topology.Defs.Basic
import Definitions.Def_LeanLevy_Levy_CharacteristicExponent
open Filter MeasureTheory Topology
open scoped NNReal
universe u v

theorem ProbabilityTheory.IsLevyProcess.charFun_marginal_cpow {Ω : Sort (u + 1)} [MeasurableSpace Ω] {E : Sort (v + 1)} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableAdd₂ E] {X : ℝ≥0 → Ω → E} {μ : Measure Ω} [IsProbabilityMeasure μ] (h : IsLevyProcess X μ) (hX : ∀ t, Measurable (X t)) :
    ∃ ε > 0, ∀ ξ ∈ Metric.ball (0 : E) ε, ∀ t : ℝ≥0,
      charFun (μ.map (X t)) ξ = (charFun (μ.map (X 1)) ξ) ^ (↑(t : ℝ) : ℂ) := by sorry
