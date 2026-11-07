-- Prove2me | Theorems.Thm_ProbabilityTheory_leanlevy_chat15_charFun_gaussian_smear_atom
-- name    : ProbabilityTheory.leanlevy_chat15_charFun_gaussian_smear_atom
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T06:41:15.666351+00:00
-- url     : https://prove2.me/theorems/1432a40b-17d2-4481-b8ce-b594ead14911
-- title:
--   Characteristic function of the Gaussian smear atom
-- statement:
--   The characteristic function of the scaled Dirac atom σ²/6 at the origin is the constant σ²/6.
-- source:
--   slink/LeanLevy 7e73fd9b23ad52956ec2756a815889a783131ce4, LeanLevy/Levy/LevyKhintchineUniqueness.lean lines 330–357, isolated Gaussian atom Fourier branch.

import Mathlib
open MeasureTheory ProbabilityTheory Complex Filter Topology
open scoped NNReal ENNReal ComplexOrder Real

theorem ProbabilityTheory.leanlevy_chat15_charFun_gaussian_smear_atom (σ_sq : ℝ≥0) (ξ : ℝ) :
    MeasureTheory.charFun (((σ_sq : ℝ≥0∞) / 6) • MeasureTheory.Measure.dirac (0 : ℝ)) ξ
      = (((σ_sq : ℝ) / 6 : ℝ) : ℂ) := by sorry
