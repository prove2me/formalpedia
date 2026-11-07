-- Prove2me | Theorems.Thm_ProbabilityTheory_leanlevy_chat15_intInt_exponent_gauss
-- name    : ProbabilityTheory.leanlevy_chat15_intInt_exponent_gauss
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T07:01:23.722271+00:00
-- url     : https://prove2.me/theorems/0dd89abe-85a1-404b-b558-6eee6ee7a175
-- title:
--   Gaussian interval smear identity
-- statement:
--   Symmetrically averaging the Gaussian quadratic component yields its shifted quadratic plus one-third mass.
-- source:
--   slink/LeanLevy 7e73fd9b23ad52956ec2756a815889a783131ce4, LeanLevy/Levy/LevyKhintchineUniqueness.lean lines 312–322, private lemma promotion.

import Mathlib
open MeasureTheory ProbabilityTheory Complex Filter Topology
open scoped NNReal ENNReal ComplexOrder Real

theorem ProbabilityTheory.leanlevy_chat15_intInt_exponent_gauss
    (s ξ : ℝ) : ∫ u in (-1 : ℝ)..1, ((s : ℂ) * (↑(ξ + u) : ℂ) ^ 2 / 2)
      = (s : ℂ) * (ξ : ℂ) ^ 2 + (s : ℂ) / 3 := by sorry
