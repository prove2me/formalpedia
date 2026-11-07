-- Prove2me | Theorems.Thm_ProbabilityTheory_leanlevy_chat16_continuous_log_unique
-- name    : ProbabilityTheory.leanlevy_chat16_continuous_log_unique
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T12:33:51.972206+00:00
-- url     : https://prove2.me/theorems/244949b6-7778-4721-a03f-b1d93798f392
-- title:
--   Continuous complex logarithms agreeing at zero are unique
-- statement:
--   If two continuous complex-valued functions on the real line agree at zero and have the same complex exponential everywhere, they coincide everywhere.
-- source:
--   slink/LeanLevy commit 7e73fd9b23ad52956ec2756a815889a783131ce4, LeanLevy/Levy/LevyKhintchineUniqueness.lean lines 566-598, original private lemma eq_of_cexp_eq_of_continuous.

import Mathlib
open MeasureTheory ProbabilityTheory

theorem ProbabilityTheory.leanlevy_chat16_continuous_log_unique
    {f g : ℝ → ℂ}
    (hf : Continuous f) (hg : Continuous g) (h0 : f 0 = g 0)
    (h : ∀ ξ, Complex.exp (f ξ) = Complex.exp (g ξ)) : f = g := by sorry
