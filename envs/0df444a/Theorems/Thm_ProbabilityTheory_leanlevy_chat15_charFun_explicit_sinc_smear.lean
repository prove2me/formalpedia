-- Prove2me | Theorems.Thm_ProbabilityTheory_leanlevy_chat15_charFun_explicit_sinc_smear
-- name    : ProbabilityTheory.leanlevy_chat15_charFun_explicit_sinc_smear
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T06:37:24.985199+00:00
-- url     : https://prove2.me/theorems/e7d88ac0-ac89-4e7b-a2b7-d4a6d7246f6c
-- title:
--   Characteristic function of explicit sinc-smeared measure
-- statement:
--   The characteristic function of a finite scaled Dirac mass plus sinc-damped density is the Gaussian-atom coefficient plus the Fourier integral of that density.
-- source:
--   slink/LeanLevy 7e73fd9b23ad52956ec2756a815889a783131ce4, LeanLevy/Levy/LevyKhintchineUniqueness.lean lines 324–369, explicit measure and finite-mass conditional reduction. Corrected only the fully qualified characteristic-function constant name, pinned to MeasureTheory.charFun.

import Mathlib
open MeasureTheory ProbabilityTheory Complex Filter Topology
open scoped NNReal ENNReal ComplexOrder Real

theorem ProbabilityTheory.leanlevy_chat15_charFun_explicit_sinc_smear (σ_sq : ℝ≥0) (ξ : ℝ)
    {ν : MeasureTheory.Measure ℝ}
    (hfin : ∫⁻ x, ENNReal.ofReal (1 - Real.sinc x) ∂ν < ⊤) :
    MeasureTheory.charFun ((((σ_sq : ℝ≥0∞) / 6) • MeasureTheory.Measure.dirac (0 : ℝ)) +
      ν.withDensity (fun x => ENNReal.ofReal (1 - Real.sinc x))) ξ
      = (((σ_sq : ℝ) / 6 : ℝ) : ℂ) +
        ∫ x, Complex.exp (↑x * ↑ξ * Complex.I) * ((1 - Real.sinc x : ℝ) : ℂ) ∂ν := by sorry
