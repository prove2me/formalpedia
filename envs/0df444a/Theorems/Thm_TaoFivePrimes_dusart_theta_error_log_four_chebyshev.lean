-- Prove2me | Theorems.Thm_TaoFivePrimes_dusart_theta_error_log_four_chebyshev
-- name    : TaoFivePrimes.dusart_theta_error_log_four_chebyshev
-- status  : Open
-- author  : @Creamycream
-- created : 2026-09-29T14:13:50.49156+00:00
-- url     : https://prove2.me/theorems/07c7db51-8952-40c4-bb60-3712b5e5ad69
-- title:
--   Dusart's global fourth-power logarithmic error bound for the Chebyshev theta function
-- statement:
--   Let the Chebyshev theta function be
--
--   $$
--   \vartheta(x)=\sum_{p\le x}\log p,
--   $$
--
--   where the sum ranges over primes. For every real number $x\ge 2$,
--
--   $$
--   |\vartheta(x)-x|\le \frac{151.3x}{(\log x)^4}.
--   $$
--
--   This is the $k=4$, $\eta_4=151.3$, $x_4=2$ entry of Dusart's explicit estimate. Dusart proves the strict inequality; the displayed non-strict form is its immediate weakening and is convenient as a reusable analytic input.
--
--   **Formalization Note** The function $\vartheta$ is represented by Mathlib's `Chebyshev.theta`.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J. 45 (2018), 227–251, Theorem 4.2, p. 237, k=4, eta=151.3, x0=2; DOI 10.1007/s11139-016-9839-4. https://piyanit.nl/wp-content/uploads/2020/10/art_10.1007_s11139-016-9839-4.pdf

import Mathlib

namespace TaoFivePrimes

theorem dusart_theta_error_log_four_chebyshev (x : ℝ) (hx : 2 ≤ x) :
    |Chebyshev.theta x - x| ≤
      (1513 / 10 : ℝ) * x / (Real.log x) ^ 4 := by sorry

end TaoFivePrimes
