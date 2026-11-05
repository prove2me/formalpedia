-- Prove2me | Theorems.Thm_ProbabilityTheory_IsLevyProcess_continuous_charFun_one
-- name    : ProbabilityTheory.IsLevyProcess.continuous_charFun_one
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T14:59:49.084144+00:00
-- url     : https://prove2.me/theorems/5ac864bf-b7ab-415d-9840-9b8131e5476f
-- title:
--   LeanLevy: ProbabilityTheory.IsLevyProcess.continuous_charFun_one
-- statement:
--   Source-header theorem from the pinned LeanLevy library. The source section parameters are made explicit. Its original proof has not been transplanted or verified.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Levy/CharacteristicExponent.lean#L213

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

theorem ProbabilityTheory.IsLevyProcess.continuous_charFun_one {Ω : Sort (u + 1)} [MeasurableSpace Ω] {E : Sort (v + 1)} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableAdd₂ E] {X : ℝ≥0 → Ω → E} {μ : Measure Ω} [IsProbabilityMeasure μ] (_hX : ∀ t, Measurable (X t)) :
    Continuous (fun ξ => charFun (μ.map (X 1)) ξ) := by sorry
