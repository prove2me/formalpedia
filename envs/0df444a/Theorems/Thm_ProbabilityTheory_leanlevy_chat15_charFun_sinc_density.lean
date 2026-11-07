-- Prove2me | Theorems.Thm_ProbabilityTheory_leanlevy_chat15_charFun_sinc_density
-- name    : ProbabilityTheory.leanlevy_chat15_charFun_sinc_density
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T06:40:28.853196+00:00
-- url     : https://prove2.me/theorems/3ed33fac-34fa-4e28-9066-4d515e593945
-- title:
--   Characteristic function of sinc-weighted density
-- statement:
--   The characteristic function of a finite sinc-weighted density is its Fourier integral against the original measure.
-- source:
--   slink/LeanLevy 7e73fd9b23ad52956ec2756a815889a783131ce4, LeanLevy/Levy/LevyKhintchineUniqueness.lean lines 336–369, isolated Fourier-density branch.

import Mathlib
open MeasureTheory ProbabilityTheory Complex Filter Topology
open scoped NNReal ENNReal ComplexOrder Real

theorem ProbabilityTheory.leanlevy_chat15_charFun_sinc_density (ξ : ℝ) {ν : MeasureTheory.Measure ℝ}
    (hfin : ∫⁻ x, ENNReal.ofReal (1 - Real.sinc x) ∂ν < ⊤) :
    MeasureTheory.charFun (ν.withDensity (fun x => ENNReal.ofReal (1 - Real.sinc x))) ξ
      = ∫ x, Complex.exp (↑x * ↑ξ * Complex.I) *
          ((1 - Real.sinc x : ℝ) : ℂ) ∂ν := by sorry
