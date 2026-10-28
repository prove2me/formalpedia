-- Prove2me | Theorems.Thm_TaoFivePrimes_prime_power_correction_nearby
-- name    : TaoFivePrimes.prime_power_correction_nearby
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T18:48:17.400131+00:00
-- url     : https://prove2.me/theorems/0205a19c-7614-4969-8dfe-6e4bbfc1a648
-- title:
--   Prime-power correction at nearby arguments above 10^18
-- statement:
--   For real $10^{18}\le x\le y$ with $\sqrt y\le1.0001\sqrt x$, the increment of $\psi-\vartheta$ is at most $0.0325\sqrt x$. The proof uses the already proved unconditional Chebyshev error bound at square-root arguments, the proved global $\psi(t)\le1.04t$ bound, and Mathlib’s Costa–Pereira inequalities. It assumes no short-prime-interval theorem or extra numerical RH input.
-- source:
--   Costa–Pereira inequalities (Mathlib Chebyshev); completed unconditional Chebyshev error estimate; used in Ramaré–Saouter (2003), Section 3.

import Mathlib

theorem TaoFivePrimes.prime_power_correction_nearby
    (x y : ℝ) (hx : (10 : ℝ)^18 ≤ x) (hxy : x ≤ y)
    (hroot : Real.sqrt y ≤ (10001/10000 : ℝ) * Real.sqrt x) :
    (Chebyshev.psi y - Chebyshev.theta y) -
      (Chebyshev.psi x - Chebyshev.theta x) ≤ (13/400 : ℝ) * Real.sqrt x := by sorry
