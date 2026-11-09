-- Prove2me | Theorems.Thm_ProbabilityTheory_leanlevy_chat24_intInt_exponent_drift
-- name    : ProbabilityTheory.leanlevy_chat24_intInt_exponent_drift
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-08T13:15:35.861776+00:00
-- url     : https://prove2.me/theorems/8be481ac-4b1c-4d41-af58-aeeea9a27151
-- title:
--   Smeared Levy exponent: drift interval-integral identity
-- statement:
--   Symmetric interval integration gives the exact drift term in the smeared Levy exponent.
-- source:
--   slink/LeanLevy commit 7e73fd9b23ad52956ec2756a815889a783131ce4, LeanLevy/Levy/LevyKhintchineUniqueness.lean, original private lemmas intInt_linear and intInt_exponent_drift

import Mathlib

open MeasureTheory ProbabilityTheory Complex
open scoped NNReal ENNReal Real

theorem ProbabilityTheory.leanlevy_chat24_intInt_exponent_drift (b ξ : ℝ) : ∫ u in (-1 : ℝ)..1, ((b : ℂ) * ↑(ξ + u) * Complex.I) = 2 * (b : ℂ) * ↑ξ * Complex.I := by sorry
