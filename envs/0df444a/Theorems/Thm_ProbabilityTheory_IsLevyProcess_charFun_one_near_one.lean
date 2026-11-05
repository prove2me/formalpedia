-- Prove2me | Theorems.Thm_ProbabilityTheory_IsLevyProcess_charFun_one_near_one
-- name    : ProbabilityTheory.IsLevyProcess.charFun_one_near_one
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T15:03:20.686903+00:00
-- url     : https://prove2.me/theorems/40d3426e-231a-4def-a6d2-87326552892e
-- title:
--   LeanLevy: ProbabilityTheory.IsLevyProcess.charFun_one_near_one
-- statement:
--   Source-header theorem from the pinned LeanLevy library. The source section parameters are made explicit. Its original proof has not been transplanted or verified.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Levy/CharacteristicExponent.lean#L226

import Init
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Basic
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Topology.Defs.Basic
import Definitions.Def_LeanLevy_Levy_CharacteristicExponent
open Filter MeasureTheory Topology
open scoped NNReal
universe u v

theorem ProbabilityTheory.IsLevyProcess.charFun_one_near_one {Ω : Sort (u + 1)} [MeasurableSpace Ω] {E : Sort (v + 1)} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableAdd₂ E] {X : ℝ≥0 → Ω → E} {μ : Measure Ω} [IsProbabilityMeasure μ] (h : IsLevyProcess X μ) (hX : ∀ t, Measurable (X t)) :
    Tendsto (fun ξ => charFun (μ.map (X 1)) ξ) (𝓝 0) (𝓝 1) := by sorry
