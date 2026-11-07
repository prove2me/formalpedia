-- Prove2me | Theorems.Thm_ProbabilityTheory_leanlevy_chat15_charFun_add_finite_measures
-- name    : ProbabilityTheory.leanlevy_chat15_charFun_add_finite_measures
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T06:46:03.667583+00:00
-- url     : https://prove2.me/theorems/ad5a3d7a-5d3b-4a1e-848a-bb973ddbcdc1
-- title:
--   Additivity of characteristic functions on finite measures
-- statement:
--   The characteristic function of the sum of two finite real measures is the sum of their characteristic functions.
-- source:
--   slink/LeanLevy 7e73fd9b23ad52956ec2756a815889a783131ce4, LeanLevy/Levy/LevyKhintchineUniqueness.lean lines 339–352, integral_add_measure Fourier decomposition generalized.

import Mathlib
open MeasureTheory ProbabilityTheory Complex Filter Topology
open scoped NNReal ENNReal ComplexOrder Real

theorem ProbabilityTheory.leanlevy_chat15_charFun_add_finite_measures
    {μ ν : MeasureTheory.Measure ℝ}
    [MeasureTheory.IsFiniteMeasure μ] [MeasureTheory.IsFiniteMeasure ν] (ξ : ℝ) :
    MeasureTheory.charFun (μ + ν) ξ = MeasureTheory.charFun μ ξ + MeasureTheory.charFun ν ξ := by sorry
