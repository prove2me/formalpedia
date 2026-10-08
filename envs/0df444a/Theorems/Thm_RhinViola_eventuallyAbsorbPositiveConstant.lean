-- Prove2me | Theorems.Thm_RhinViola_eventuallyAbsorbPositiveConstant
-- name    : RhinViola.eventuallyAbsorbPositiveConstant
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-05T11:04:49.424596+00:00
-- url     : https://prove2.me/theorems/c35534b1-43e0-4102-b42d-7256b29b47b8
-- title:
--   Positive constants are absorbed by strict exponent slack
-- statement:
--   If C>0 and E<T, then for all sufficiently large positive natural q, q^(-T)<C q^(-E). Equivalently, the positive fixed constant C can be absorbed into any strict exponent slack T-E. This is the final constant-absorption step used in Rhin and Viola's irrationality-measure criterion.
-- source:
--   Elementary real-power consequence used in G. Rhin and C. Viola, On the irrationality measure of ζ(2), Annales de l'Institut Fourier 43 (1993), pp. 91–92, Lemma 4.

import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

theorem RhinViola.eventuallyAbsorbPositiveConstant
    (C E T : ℝ) (hC : 0 < C) (hET : E < T) :
    ∃ Q : ℕ, ∀ q : ℕ, Q ≤ q → 0 < q →
      (q : ℝ) ^ (-T) < C * (q : ℝ) ^ (-E) := by sorry
