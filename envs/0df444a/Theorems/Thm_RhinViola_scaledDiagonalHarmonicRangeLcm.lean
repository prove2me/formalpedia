-- Prove2me | Theorems.Thm_RhinViola_scaledDiagonalHarmonicRangeLcm
-- name    : RhinViola.scaledDiagonalHarmonicRangeLcm
-- status  : Open
-- author  : @WillR
-- created : 2026-10-06T11:47:41.145786+00:00
-- url     : https://prove2.me/theorems/011a851a-0772-4e9e-bae3-5be744af9e5a
-- title:
--   Range-lcm denominator clearing for the diagonal reciprocal-square block
-- statement:
--   Let D be the lcm of 1,...,n. If h<n, then D^2 clears every denominator in the finite reciprocal-square block 1+1/2^2+...+1/h^2, leaving the explicit natural integer sum of squared quotients.
-- source:
--   Diagonal denominator control in G. Rhin and C. Viola, On the irrationality measure of zeta(2), Annales de l'Institut Fourier 43 (1993), Section 3.

import Theorems.Thm_RhinViola_rangeLcmDivides
import Theorems.Thm_RhinViola_scaledReciprocalSquareBlockNat
import Mathlib.Tactic

theorem RhinViola.scaledDiagonalHarmonicRangeLcm
    (n h : ℕ) (hhn : h < n) :
    let D := (Finset.range n).lcm (fun i : ℕ => i + 1)
    (D : ℝ) ^ 2 *
        (Finset.sum (Finset.range h) (fun j : ℕ =>
          (1 : ℝ) / ((((j + 1 : ℕ) : ℝ)) ^ 2))) =
      ((Finset.sum (Finset.range h) (fun j : ℕ =>
          (D / (j + 1)) ^ 2) : ℕ) : ℝ) := by sorry
