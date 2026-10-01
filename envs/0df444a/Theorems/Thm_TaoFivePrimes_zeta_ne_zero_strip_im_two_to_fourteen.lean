-- Prove2me | Theorems.Thm_TaoFivePrimes_zeta_ne_zero_strip_im_two_to_fourteen
-- name    : TaoFivePrimes.zeta_ne_zero_strip_im_two_to_fourteen
-- status  : Open
-- author  : @Gabewhigham
-- created : 2026-09-30T14:23:36.467906+00:00
-- url     : https://prove2.me/theorems/ac5b0112-ba7e-4990-90ee-e14ca8d1ef91
-- title:
--   $\zeta(s)\ne0$ for $0<\operatorname{Re}(s)<1$, $2\le\operatorname{Im}(s)\le14$
-- statement:
--   **No zeros of $\zeta$ below height $14$ (beyond $2$).** For every $s\in\mathbb C$ with
--
--   $$0<\operatorname{Re}(s)<1,\qquad 2\le \operatorname{Im}(s)\le 14,$$
--
--   we have $\zeta(s)\neq 0$.
--
--   The lowest non-trivial zero of $\zeta$ is $\tfrac12 + i\,14.134725\ldots$, so the rectangle above is zero-free. Together with the already proved zero-free rectangle $|\operatorname{Im}(s)|\le 2$ (`zeta_ne_zero_of_mem_strip_of_abs_im_le_two`) this gives the bottom block $0\le\operatorname{Im}(s)\le14$ of the numerical verification of the Riemann hypothesis up to height $3.29\times10^9$ (Tao, Theorem 1.5). It is a small, self-contained computation (an explicit lower bound for $|\zeta|$ or the argument principle on a rectangle).
-- source:
--   Lowest zero ordinate 14.134725... (Gram 1903; see A. M. Odlyzko's tables of zeros and E. C. Titchmarsh, The Theory of the Riemann Zeta-Function, 2nd ed., Section 15.1); bottom block of Theorem 1.5 (p. 7) of T. Tao, Every odd number greater than 1 is the sum of at most five primes, Math. Comp. 83 (2014), 997-1038, https://arxiv.org/abs/1201.6656.

import Mathlib

namespace TaoFivePrimes

theorem zeta_ne_zero_strip_im_two_to_fourteen (s : ℂ) (h0 : 0 < s.re) (h1 : s.re < 1)
    (ha : 2 ≤ s.im) (hb : s.im ≤ 14) : riemannZeta s ≠ 0 := by
  sorry

end TaoFivePrimes
