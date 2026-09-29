-- Prove2me | Theorems.Thm_TaoFivePrimes_reciprocal_primes_theta_tail_identity
-- name    : TaoFivePrimes.reciprocal_primes_theta_tail_identity
-- status  : Open
-- author  : @xuanji
-- created : 2026-09-27T22:42:25.865695+00:00
-- url     : https://prove2.me/theorems/42cfb683-0b1f-4c44-aa63-035298f9dd7f
-- title:
--   Exact reciprocal-prime remainder as a Chebyshev theta tail
-- statement:
--   For $x\ge2$, let $\theta(x)=\sum_{p\le x}\log p$, and let $B=\gamma+\sum_p(\log(1-1/p)+1/p)$. Then
--
--   $$\sum_{p\le x}\frac1p=\log\log x+B+\frac{\theta(x)-x}{x\log x}-\int_x^\infty\frac{(\theta(t)-t)(1+\log t)}{t^2\log^2 t}\,dt.$$
--
--   This exact identity transfers estimates for the Chebyshev remainder into explicit estimates for reciprocal-prime sums.
-- source:
--   R. Vanlalngaia (Ramdinmawia), Explicit Mertens Sums, INTEGERS 17 (2017), A11, p. 9, equation (17) and the immediately following identity for B. https://emis.de/ft/19485

import Mathlib

theorem TaoFivePrimes.reciprocal_primes_theta_tail_identity (x : ℝ) (hx : 2 ≤ x) :
    (∑ p ∈ Nat.primesLE ⌊x⌋₊, 1 / (p : ℝ)) =
      Real.log (Real.log x) +
        (Real.eulerMascheroniConstant +
          ∑' p : Nat.Primes, (Real.log (1 - 1 / (p : ℝ)) + 1 / (p : ℝ))) +
      ((∑ p ∈ Nat.primesLE ⌊x⌋₊, Real.log (p : ℝ)) - x) / (x * Real.log x) -
      ∫ t in Set.Ioi x,
        (((∑ p ∈ Nat.primesLE ⌊t⌋₊, Real.log (p : ℝ)) - t) *
          (Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2)) := by sorry
