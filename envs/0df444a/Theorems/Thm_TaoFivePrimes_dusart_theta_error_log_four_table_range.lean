-- Prove2me | Theorems.Thm_TaoFivePrimes_dusart_theta_error_log_four_table_range
-- name    : TaoFivePrimes.dusart_theta_error_log_four_table_range
-- status  : Open
-- author  : @Creamycream
-- created : 2026-09-29T17:48:03.917277+00:00
-- url     : https://prove2.me/theorems/6cb4679f-3f68-421c-9ad0-bc647ad663b8
-- title:
--   Dusart theta error through the last tabulated exponent
-- statement:
--   For every real $x$ with $2 \le x \le e^{13900}$, the Chebyshev theta function satisfies
--   $$|\vartheta(x)-x|\le \frac{151.3x}{\log^4 x}.$$
--   This is the finite-and-tabulated part of Dusart's Theorem 4.2: direct inspection handles the small range, and Proposition 3.2 together with Table 1 and the Rosser-Schoenfeld bound for $|\psi-\vartheta|$ handles successive exponential intervals through the final row $b=13900$.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J. 45 (2018), 227-251, Theorem 4.2 and its proof, pp. 234-237; Table 1 through b = 13900 and the large-value argument citing [10, Theorem 1.1]. DOI 10.1007/s11139-016-9839-4. https://piyanit.nl/wp-content/uploads/2020/10/art_10.1007_s11139-016-9839-4.pdf

import Mathlib.NumberTheory.Chebyshev

namespace TaoFivePrimes

theorem dusart_theta_error_log_four_table_range (x : ℝ)
    (hx : 2 ≤ x) (hupper : x ≤ Real.exp 13900) :
    |Chebyshev.theta x - x| ≤
      (1513 / 10 : ℝ) * x / (Real.log x) ^ 4 := by sorry

end TaoFivePrimes
