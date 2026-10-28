-- Prove2me | Theorems.Thm_TaoFivePrimes_zeta_zero_free_rectangle_106_106p36
-- name    : TaoFivePrimes.zeta_zero_free_rectangle_106_106p36
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-27T17:27:01.099987+00:00
-- url     : https://prove2.me/theorems/06c1df0b-7af3-4a95-90d9-c0df3a6f807d
-- title:
--   Zeta is zero-free in the critical-strip rectangle at heights 106 to 106.36
-- statement:
--   The Riemann zeta function has no zero in the critical strip whose imaginary part lies between $106$ and $106.36$, including both endpoints. More precisely, if $s=\sigma+it$ satisfies $0<\sigma<1$ and $106\le t\le 2659/25$, then
--
--   $$
--   \zeta(s)\ne0.
--   $$
--
--   This zero-free rectangle extends the already certified low-height information used in the finite verification of zeros for Tao's five-primes argument.
-- source:
--   Derived from the existing Prove2Me certified xi approximation at height 105.5, TaoFivePrimes.rh105to106_xi_approximation (f1a997b6-e3bc-4e80-a6ec-bf7b7f42c918), by a new Bernstein rectangle certificate. The local xi/Mellin and numerical certificate methods originate in Prove2Me submissions by sometik179 and Gabewhigham; generic Bernstein lemmas adapted from submission f32249e2-6b1c-47ef-8195-015259f0d044. Related finite zero verification: D. J. Platt, Isolating some non-trivial zeros of zeta, Math. Comp. 86 (2017), 2449–2467, and T. Tao, Every odd number greater than 1 is the sum of at most five primes, arXiv:1201.6656v4, Theorem 1.5, https://arxiv.org/html/1201.6656v4. The stated rectangle and proof are derived here, not a verbatim quotation.

import Mathlib.NumberTheory.LSeries.RiemannZeta

theorem TaoFivePrimes.zeta_zero_free_rectangle_106_106p36 (s : ℂ) (h0 : 0 < s.re) (h1 : s.re < 1)
    (ha : 106 ≤ s.im) (hb : s.im ≤ (2659/25:ℝ)) : riemannZeta s ≠ 0 := by sorry
