-- Prove2me | Theorems.Thm_ProbabilityTheory_leanlevy_chat24_intInt_exponent_gauss
-- name    : ProbabilityTheory.leanlevy_chat24_intInt_exponent_gauss
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-08T13:15:28.496276+00:00
-- url     : https://prove2.me/theorems/b72a2525-4999-47e0-bebc-f20e4d4d0beb
-- title:
--   Smeared Levy exponent: gauss interval-integral identity
-- statement:
--   Symmetric interval integration gives the exact Gaussian term, including the variance over three, in the smeared Levy exponent.
-- source:
--   slink/LeanLevy commit 7e73fd9b23ad52956ec2756a815889a783131ce4, LeanLevy/Levy/LevyKhintchineUniqueness.lean, original private lemmas intInt_quadratic and intInt_exponent_gauss

import Mathlib

open MeasureTheory ProbabilityTheory Complex
open scoped NNReal ENNReal Real

theorem ProbabilityTheory.leanlevy_chat24_intInt_exponent_gauss (s ξ : ℝ) : ∫ u in (-1 : ℝ)..1, ((s : ℂ) * (↑(ξ + u) : ℂ) ^ 2 / 2) = (s : ℂ) * (ξ : ℂ) ^ 2 + (s : ℂ) / 3 := by sorry
