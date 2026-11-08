-- Prove2me | Theorems.Thm_ProbabilityTheory_IsLevyProcess_charFun_marginal_nat_mul
-- name    : ProbabilityTheory.IsLevyProcess.charFun_marginal_nat_mul
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T15:10:31.329064+00:00
-- url     : https://prove2.me/theorems/2d876ad9-a611-474b-b232-f3a3440b4005
-- title:
--   LeanLevy: ProbabilityTheory.IsLevyProcess.charFun_marginal_nat_mul
-- statement:
--   Source-header theorem from the pinned LeanLevy library. The source section parameters are made explicit. Its original proof has not been transplanted or verified.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Levy/CharacteristicExponent.lean#L280

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

theorem ProbabilityTheory.IsLevyProcess.charFun_marginal_nat_mul {Ω : Sort (u + 1)} [MeasurableSpace Ω] {E : Sort (v + 1)} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableAdd₂ E] {X : ℝ≥0 → Ω → E} {μ : Measure Ω} [IsProbabilityMeasure μ] (h : IsLevyProcess X μ) (hX : ∀ t, Measurable (X t))
    (n : ℕ) (s : ℝ≥0) (ξ : E) :
    charFun (μ.map (X ((n : ℝ≥0) * s))) ξ = (charFun (μ.map (X s)) ξ) ^ n := by sorry
