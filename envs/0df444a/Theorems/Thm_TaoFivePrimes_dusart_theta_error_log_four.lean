-- Prove2me | Theorems.Thm_TaoFivePrimes_dusart_theta_error_log_four
-- name    : TaoFivePrimes.dusart_theta_error_log_four
-- status  : Open
-- author  : @xuanji
-- created : 2026-09-27T23:11:56.128112+00:00
-- url     : https://prove2.me/theorems/c1e0bf7d-a67f-4a03-830f-38b285a1f64e
-- title:
--   Dusart global fourth-power logarithmic theta error
-- statement:
--   For every real $x\ge2$, the Chebyshev theta function satisfies
--   $$|\vartheta(x)-x|\le\frac{151.3x}{\log^4x},\qquad\vartheta(x)=\sum_{p\le x}\log p.$$
--   This is the $k=4$ entry of Dusart's explicit theta estimate, stated with a non-strict inequality. It supplies a single global analytic input for the mission's large-range reciprocal-prime bounds. The constant can be weakened to $160$; Abel partial summation then bounds their error by $40/\log^4x+192/\log^5x$, which is at most $4/\log^3x$ when $x\ge10^8$. Thus this input avoids the additional finite-range improvement needed for the sharper coefficient $100$. The explicit prime-distribution estimate itself remains to be formally proved.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018), 227–251, Theorem4.2, k=4 eta=151.3 x0=2; DOI10.1007/s11139-016-9839-4. https://piyanit.nl/wp-content/uploads/2020/10/art_10.1007_s11139-016-9839-4.pdf. Also quoted explicitly in Christian Axler, Integers18 (2018), A52, Lemma1 table, p.5, https://math.colgate.edu/~integers/s52/s52.pdf.

import Mathlib

theorem TaoFivePrimes.dusart_theta_error_log_four (x : ℝ) (hx : 2 ≤ x) :
  |(∑ p ∈ Nat.primesLE ⌊x⌋₊, Real.log (p : ℝ)) - x| ≤
    (1513 / 10 : ℝ) * x / (Real.log x) ^ 4 := by sorry
