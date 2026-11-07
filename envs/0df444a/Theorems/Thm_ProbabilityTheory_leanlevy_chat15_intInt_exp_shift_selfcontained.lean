-- Prove2me | Theorems.Thm_ProbabilityTheory_leanlevy_chat15_intInt_exp_shift_selfcontained
-- name    : ProbabilityTheory.leanlevy_chat15_intInt_exp_shift_selfcontained
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T07:10:55.430738+00:00
-- url     : https://prove2.me/theorems/38a404a8-5461-4399-887c-b09d06048eef
-- title:
--   Self-contained symmetric exponential interval shift
-- statement:
--   The Fourier integral of a shifted exponential over [-1,1] factors as the phase at xi times twice sinc x.
-- source:
--   slink/LeanLevy 7e73fd9b23ad52956ec2756a815889a783131ce4, LeanLevy/Levy/LevyKhintchineProof.lean lines 1458–1490 and LevyKhintchineUniqueness.lean lines 152–169, exact source expansion.

import Mathlib
open MeasureTheory ProbabilityTheory Complex Filter Topology
open scoped NNReal ENNReal ComplexOrder Real

theorem ProbabilityTheory.leanlevy_chat15_intInt_exp_shift_selfcontained (ξ x : ℝ) :
    ∫ u in (-1 : ℝ)..1, Complex.exp (↑x * ↑(ξ + u) * Complex.I)
      = Complex.exp (↑x * ↑ξ * Complex.I) * (2 * (Real.sinc x : ℂ)) := by sorry
