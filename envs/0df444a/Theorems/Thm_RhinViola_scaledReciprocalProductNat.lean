-- Prove2me | Theorems.Thm_RhinViola_scaledReciprocalProductNat
-- name    : RhinViola.scaledReciprocalProductNat
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-05T20:34:47.175502+00:00
-- url     : https://prove2.me/theorems/fc8588bc-d687-408c-8eab-7ba5d091fef8
-- title:
--   Denominator clearing for a product of two reciprocal divisors
-- statement:
--   If positive natural numbers r and s both divide D, then multiplying 1/(rs) by D^2 clears both denominators exactly: D^2/(rs)=(D/r)(D/s), a natural integer. This is the atomic denominator-clearing fact used in the Rhin-Viola monomial arithmetic bridge.
-- source:
--   Elementary divisibility step used in G. Rhin and C. Viola, On the irrationality measure of zeta(2), Annales de l'Institut Fourier 43 (1993), Section 3.

import Mathlib.Data.Nat.Cast.Field
import Mathlib.Tactic

theorem RhinViola.scaledReciprocalProductNat
    (D r s : ℕ) (hr : r ∣ D) (hs : s ∣ D)
    (hrpos : 0 < r) (hspos : 0 < s) :
    (D : ℝ) ^ 2 * ((1 : ℝ) / (r : ℝ)) * ((1 : ℝ) / (s : ℝ)) =
      ((((D / r) * (D / s) : ℕ) : ℝ)) := by sorry
