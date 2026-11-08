-- Prove2me | Theorems.Thm_ProbabilityTheory_IsLevyProcess_continuous_charFun_marginal_t
-- name    : ProbabilityTheory.IsLevyProcess.continuous_charFun_marginal_t
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T15:11:53.341099+00:00
-- url     : https://prove2.me/theorems/9c016800-17fa-4529-a60d-9516a0e29c2b
-- title:
--   LeanLevy: ProbabilityTheory.IsLevyProcess.continuous_charFun_marginal_t
-- statement:
--   Source-header theorem from the pinned LeanLevy library. The source section parameters are made explicit. Its original proof has not been transplanted or verified.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Levy/CharacteristicExponent.lean#L517

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

theorem ProbabilityTheory.IsLevyProcess.continuous_charFun_marginal_t {Ω : Sort (u + 1)} [MeasurableSpace Ω] {E : Sort (v + 1)} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableAdd₂ E] {X : ℝ≥0 → Ω → E} {μ : Measure Ω} [IsProbabilityMeasure μ] (h : IsLevyProcess X μ)
    (hX : ∀ t, Measurable (X t)) (ξ : E) :
    Continuous (fun t : ℝ≥0 => charFun (μ.map (X t)) ξ) := by sorry
