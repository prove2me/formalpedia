-- Prove2me | Theorems.Thm_ProbabilityTheory_leanlevy_chat15_sinc_withDensity_finite_from_lintegral
-- name    : ProbabilityTheory.leanlevy_chat15_sinc_withDensity_finite_from_lintegral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T06:28:35.731978+00:00
-- url     : https://prove2.me/theorems/29ed56fe-59ed-4499-8505-a6680b9780ed
-- title:
--   Finite sinc-weighted measure from finite density mass
-- statement:
--   A measure weighted by one minus sinc has finite total mass whenever the corresponding nonnegative lintegral is finite.
-- source:
--   slink/LeanLevy 7e73fd9b23ad52956ec2756a815889a783131ce4, LeanLevy/Levy/LevyKhintchineUniqueness.lean lines 335–338, source-exact simplification of the withDensity finite-measure argument.

import Mathlib
open MeasureTheory ProbabilityTheory Complex Filter Topology
open scoped NNReal ENNReal ComplexOrder Real

theorem ProbabilityTheory.leanlevy_chat15_sinc_withDensity_finite_from_lintegral {ν : MeasureTheory.Measure ℝ}
    (h : ∫⁻ x, ENNReal.ofReal (1 - Real.sinc x) ∂ν < ⊤) :
    MeasureTheory.IsFiniteMeasure (ν.withDensity (fun x => ENNReal.ofReal (1 - Real.sinc x))) := by sorry
