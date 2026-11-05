-- Prove2me | Theorems.Thm_ProbabilityTheory_IsLevyProcess_charFun_one_zero
-- name    : ProbabilityTheory.IsLevyProcess.charFun_one_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T15:01:01.270355+00:00
-- url     : https://prove2.me/theorems/db0e1532-68e7-4025-82be-b01fd37ad6eb
-- title:
--   LeanLevy: ProbabilityTheory.IsLevyProcess.charFun_one_zero
-- statement:
--   Source-header theorem from the pinned LeanLevy library. The source section parameters are made explicit. Its original proof has not been transplanted or verified.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Levy/CharacteristicExponent.lean#L219

import Init
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Topology.Defs.Basic
import Definitions.Def_LeanLevy_Levy_CharacteristicExponent
open MeasureTheory Topology
open scoped NNReal
universe u v

theorem ProbabilityTheory.IsLevyProcess.charFun_one_zero {Ω : Sort (u + 1)} [MeasurableSpace Ω] {E : Sort (v + 1)} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableAdd₂ E] {X : ℝ≥0 → Ω → E} {μ : Measure Ω} [IsProbabilityMeasure μ] (_h : IsLevyProcess X μ) (hX : ∀ t, Measurable (X t)) :
    charFun (μ.map (X 1)) (0 : E) = 1 := by sorry
