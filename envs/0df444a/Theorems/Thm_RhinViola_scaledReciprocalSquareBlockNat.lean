-- Prove2me | Theorems.Thm_RhinViola_scaledReciprocalSquareBlockNat
-- name    : RhinViola.scaledReciprocalSquareBlockNat
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-05T23:36:32.209148+00:00
-- url     : https://prove2.me/theorems/043ccfcd-87cb-4bf6-9807-782b70caaa67
-- title:
--   Exact denominator clearing for a finite reciprocal-square block
-- statement:
--   If every denominator 1,...,h divides D, then D^2 times the finite reciprocal-square sum through h is exactly the natural integer sum of (D/(j+1))^2.
-- source:
--   Diagonal denominator control in G. Rhin and C. Viola, On the irrationality measure of zeta(2), Annales de l'Institut Fourier 43 (1993), Section 3.

import Theorems.Thm_RhinViola_scaledReciprocalSquareNat
import Mathlib.Tactic
open scoped BigOperators

theorem RhinViola.scaledReciprocalSquareBlockNat
    (D h : ℕ)
    (hdiv : ∀ j : ℕ, j < h → j + 1 ∣ D) :
    (D : ℝ) ^ 2 *
        (Finset.sum (Finset.range h) (fun j : ℕ =>
          (1 : ℝ) / ((((j + 1 : ℕ) : ℝ)) ^ 2))) =
      ((Finset.sum (Finset.range h) (fun j : ℕ =>
          (D / (j + 1)) ^ 2) : ℕ) : ℝ) := by sorry
