-- Prove2me | Theorems.Thm_TaoFivePrimes_normalized_oscillatory_second_difference
-- name    : TaoFivePrimes.normalized_oscillatory_second_difference
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-27T21:28:07.184991+00:00
-- url     : https://prove2.me/theorems/b07b737e-79d6-4da0-a1b3-8e74b4f5a69d
-- title:
--   Oscillatory second-difference bound for small multiplicative shifts
-- statement:
--   For $0\le r\le1/3$, $0\le\alpha\le3$, and $\gamma\in\mathbb R$, set
--
--   $$
--   F_\pm=(1\pm r)^\alpha e^{i\gamma\log(1\pm r)}.
--   $$
--
--   Then
--
--   $$
--   |F_+-2+F_-|\le4\sin^2(\gamma r/2)+8r+3|\gamma|r^2.
--   $$
--
--   The estimate retains the oscillation in the central second difference and can be used to refine a smoothed explicit-formula zero sum.
-- source:
--   Elementary analytic estimate developed for the Tao five-primes Chebyshev-error reduction.

import Mathlib

theorem TaoFivePrimes.normalized_oscillatory_second_difference
    (r α γ : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1/3) (ha0 : 0 ≤ α) (ha3 : α ≤ 3) :
    ‖(((1+r)^α:ℝ):ℂ)*Complex.exp (((γ*Real.log (1+r):ℝ):ℂ)*Complex.I)-2+
      (((1-r)^α:ℝ):ℂ)*Complex.exp (((γ*Real.log (1-r):ℝ):ℂ)*Complex.I)‖ ≤
      4*(Real.sin (γ*r/2))^2 + 8*r + 3 * |γ| * r^2 := by sorry
