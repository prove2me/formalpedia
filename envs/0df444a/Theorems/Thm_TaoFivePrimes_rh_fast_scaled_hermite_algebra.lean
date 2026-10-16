-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_fast_scaled_hermite_algebra
-- name    : TaoFivePrimes.rh_fast_scaled_hermite_algebra
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-16T09:36:09.948506+00:00
-- url     : https://prove2.me/theorems/b20c13a2-05ea-4ed1-91bd-699bc850fedd
-- title:
--   TaoFivePrimes.rh_fast_scaled_hermite_algebra
-- statement:
--   Real Hermite evaluation agrees with complex evaluation on a real argument, and the public scaled Hermite functions satisfy the exact two-step recurrence. No numerical or RH enclosure is asserted.
-- source:
--   Platt, Isolating some non-trivial zeros of zeta, DOI10.1090/mcom/3198; Gaussian/Hermite Fourier identities and center Stirling expansion. Original surrounding attribution retained: sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Definitions.Def_TaoFivePrimes_RHFastGaussianWindowFourier

theorem TaoFivePrimes.rh_fast_scaled_hermite_algebra (n:Nat) (x:ℝ) :
 Polynomial.aeval (x:ℂ) (Polynomial.hermite n)=
   (((Polynomial.hermite n).eval₂ (Int.castRingHom ℝ) x:ℝ):ℂ) ∧
 RHFastGaussianWindow.scaledHermite (n+2) x=
  ((5/64:ℝ)*x)*RHFastGaussianWindow.scaledHermite (n+1) x-
   ((n+1:Nat):ℝ)*(5/64:ℝ)^2*RHFastGaussianWindow.scaledHermite n x := by sorry
