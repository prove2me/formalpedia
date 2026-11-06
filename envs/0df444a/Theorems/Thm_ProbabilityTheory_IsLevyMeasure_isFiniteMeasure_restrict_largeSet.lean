-- Prove2me | Theorems.Thm_ProbabilityTheory_IsLevyMeasure_isFiniteMeasure_restrict_largeSet
-- name    : ProbabilityTheory.IsLevyMeasure.isFiniteMeasure_restrict_largeSet
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T15:40:59.680204+00:00
-- url     : https://prove2.me/theorems/4668d567-6d85-4b9d-9907-440747f05608
-- title:
--   LeanLevy: ProbabilityTheory.IsLevyMeasure.isFiniteMeasure_restrict_largeSet
-- statement:
--   Source-header theorem from the pinned LeanLevy library. The source section variables are declared in the preamble. Its original proof has not been transplanted or verified.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Levy/LevyKhintchineProof.lean#L2125

import Init
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Definitions.Def_LeanLevy_Levy_CharacteristicExponent
import Definitions.Def_LeanLevy_Levy_LevyKhintchine
import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof
import Definitions.Def_LeanLevy_Levy_LevyKhintchineUniqueness
open MeasureTheory Complex ComplexConjugate Set Filter Topology Finset ProbabilityTheory
open scoped NNReal ENNReal

theorem ProbabilityTheory.IsLevyMeasure.isFiniteMeasure_restrict_largeSet {ν : Measure ℝ} (hν : IsLevyMeasure ν)
    {ε : ℝ} (hε : 0 < ε) : IsFiniteMeasure (ν.restrict (largeSet ε)) := by sorry
