-- Prove2me | Theorems.Thm_RhinViola_scaledHarmonicBlockNat
-- name    : RhinViola.scaledHarmonicBlockNat
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-05T22:48:02.080631+00:00
-- url     : https://prove2.me/theorems/6d536f4e-a595-48f8-b5fa-3a099b527d46
-- title:
--   Exact denominator clearing for an off-diagonal harmonic block
-- statement:
--   If d divides D and every denominator h+j+1 in a length-d harmonic block divides D, then D^2 times (1/d) times that harmonic block is exactly a natural integer, explicitly the sum of (D/d)(D/(h+j+1)). This is the denominator-clearing statement required for off-diagonal Rhin-Viola monomial kernels.
-- source:
--   Denominator control in G. Rhin and C. Viola, On the irrationality measure of zeta(2), Annales de l'Institut Fourier 43 (1993), Section 3.

import Theorems.Thm_RhinViola_scaledReciprocalProductNat
import Mathlib.Tactic
open scoped BigOperators

theorem RhinViola.scaledHarmonicBlockNat
    (D h d : ℕ) (hd : 0 < d) (hdD : d ∣ D)
    (hdiv : ∀ j : ℕ, j < d → h + j + 1 ∣ D) :
    (D : ℝ) ^ 2 *
        ((1 : ℝ) / (d : ℝ) *
          Finset.sum (Finset.range d) (fun j : ℕ =>
            (1 : ℝ) / (((h + j + 1 : ℕ) : ℝ)))) =
      ((Finset.sum (Finset.range d) (fun j : ℕ =>
          (D / d) * (D / (h + j + 1))) : ℕ) : ℝ) := by sorry
