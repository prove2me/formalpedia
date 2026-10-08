-- Prove2me | Theorems.Thm_RhinViola_scaledReciprocalSquareNat
-- name    : RhinViola.scaledReciprocalSquareNat
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-05T22:47:36.423919+00:00
-- url     : https://prove2.me/theorems/7b234813-4b8d-45ee-8a65-cee42180a589
-- title:
--   Denominator clearing for a reciprocal square
-- statement:
--   If positive r divides D, then D^2/r^2=(D/r)^2, so D^2 clears the reciprocal-square denominator exactly and leaves a natural integer.
-- source:
--   Elementary denominator-clearing step used in G. Rhin and C. Viola, On the irrationality measure of zeta(2), Annales de l'Institut Fourier 43 (1993), Section 3.

import Theorems.Thm_RhinViola_scaledReciprocalProductNat
import Mathlib.Tactic

theorem RhinViola.scaledReciprocalSquareNat
    (D r : ℕ) (hr : r ∣ D) (hrpos : 0 < r) :
    (D : ℝ) ^ 2 * ((1 : ℝ) / ((r : ℝ) ^ 2)) =
      ((((D / r) ^ 2 : ℕ) : ℝ)) := by sorry
