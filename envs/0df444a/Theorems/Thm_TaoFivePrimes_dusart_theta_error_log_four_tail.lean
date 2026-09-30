-- Prove2me | Theorems.Thm_TaoFivePrimes_dusart_theta_error_log_four_tail
-- name    : TaoFivePrimes.dusart_theta_error_log_four_tail
-- status  : Open
-- author  : @Creamycream
-- created : 2026-09-29T17:48:06.061479+00:00
-- url     : https://prove2.me/theorems/bf882dbf-bff9-496e-b39f-16e2be21e218
-- title:
--   Dusart theta error beyond the tabulated range
-- statement:
--   For every real $x\ge e^{13900}$, the Chebyshev theta function satisfies
--   $$|\vartheta(x)-x|\le \frac{151.3x}{\log^4 x}.$$
--   This is the large-value part of Dusart's Theorem 4.2, obtained in the paper from the explicit zero-free-region estimate cited as [10, Theorem 1.1], combined with the bound for $|\psi(x)-\vartheta(x)|$.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J. 45 (2018), 227-251, Theorem 4.2 and its proof, pp. 234-237; Table 1 through b = 13900 and the large-value argument citing [10, Theorem 1.1]. DOI 10.1007/s11139-016-9839-4. https://piyanit.nl/wp-content/uploads/2020/10/art_10.1007_s11139-016-9839-4.pdf

import Mathlib.NumberTheory.Chebyshev

namespace TaoFivePrimes

theorem dusart_theta_error_log_four_tail (x : ℝ)
    (hx : Real.exp 13900 ≤ x) :
    |Chebyshev.theta x - x| ≤
      (1513 / 10 : ℝ) * x / (Real.log x) ^ 4 := by sorry

end TaoFivePrimes
