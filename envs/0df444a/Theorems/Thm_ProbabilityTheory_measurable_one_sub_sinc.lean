-- Prove2me | Theorems.Thm_ProbabilityTheory_measurable_one_sub_sinc
-- name    : ProbabilityTheory.measurable_one_sub_sinc
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T15:51:24.900058+00:00
-- url     : https://prove2.me/theorems/4709a059-ac96-4e71-8960-be616308d508
-- title:
--   LeanLevy: ProbabilityTheory.measurable_one_sub_sinc
-- statement:
--   Source-header theorem from the pinned LeanLevy library. The source section variables are declared in the preamble. Its original proof has not been transplanted or verified.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Levy/LevyKhintchineUniqueness.lean#L82

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
open MeasureTheory Complex ComplexConjugate Set Filter Topology Finset ProbabilityTheory
open scoped NNReal ENNReal

theorem ProbabilityTheory.measurable_one_sub_sinc :
    Measurable fun x : ℝ => ENNReal.ofReal (1 - Real.sinc x) := by sorry
