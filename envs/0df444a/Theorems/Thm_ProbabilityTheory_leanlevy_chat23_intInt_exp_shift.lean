-- Prove2me | Theorems.Thm_ProbabilityTheory_leanlevy_chat23_intInt_exp_shift
-- name    : ProbabilityTheory.leanlevy_chat23_intInt_exp_shift
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-08T12:41:21.498759+00:00
-- url     : https://prove2.me/theorems/ce401989-9c98-46fc-9dad-7c7e8cab40c8
-- title:
--   Shifted symmetric exponential interval-integral identity
-- statement:
--   The interval integral of exp(ix(ξ+u)) factors as exp(ixξ) times twice sinc x over the symmetric unit interval.
-- source:
--   slink/LeanLevy commit 7e73fd9b23ad52956ec2756a815889a783131ce4, LevyKhintchineUniqueness.lean lines 152-171

import Mathlib

open MeasureTheory ProbabilityTheory Complex
open scoped NNReal ENNReal Real

theorem ProbabilityTheory.leanlevy_chat23_intInt_exp_shift (ξ x : ℝ) :
    ∫ u in (-1 : ℝ)..1, Complex.exp (↑x * ↑(ξ + u) * Complex.I)
      = Complex.exp (↑x * ↑ξ * Complex.I) * (2 * (Real.sinc x : ℂ)) := by sorry
