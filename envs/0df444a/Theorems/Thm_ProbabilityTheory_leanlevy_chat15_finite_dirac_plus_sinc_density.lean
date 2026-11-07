-- Prove2me | Theorems.Thm_ProbabilityTheory_leanlevy_chat15_finite_dirac_plus_sinc_density
-- name    : ProbabilityTheory.leanlevy_chat15_finite_dirac_plus_sinc_density
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T06:29:20.73923+00:00
-- url     : https://prove2.me/theorems/f269d73b-9a99-44db-ace0-72ad2e1a301e
-- title:
--   Finite Dirac atom plus sinc-weighted measure
-- statement:
--   An atom with finite coefficient added to the sinc-weighted jump measure is finite when its nonnegative sinc density has finite total mass.
-- source:
--   slink/LeanLevy 7e73fd9b23ad52956ec2756a815889a783131ce4, LeanLevy/Levy/LevyKhintchineUniqueness.lean lines 101–110, explicit Dirac coefficient variant.

import Mathlib
open MeasureTheory ProbabilityTheory Complex Filter Topology
open scoped NNReal ENNReal ComplexOrder Real

theorem ProbabilityTheory.leanlevy_chat15_finite_dirac_plus_sinc_density
    (a : ℝ≥0∞) (ha : a < ⊤) {ν : MeasureTheory.Measure ℝ}
    (h : ∫⁻ x, ENNReal.ofReal (1 - Real.sinc x) ∂ν < ⊤) :
    MeasureTheory.IsFiniteMeasure (a • MeasureTheory.Measure.dirac (0 : ℝ) +
      ν.withDensity (fun x => ENNReal.ofReal (1 - Real.sinc x))) := by sorry
