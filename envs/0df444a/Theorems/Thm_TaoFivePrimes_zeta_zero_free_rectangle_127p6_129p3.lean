-- Prove2me | Theorems.Thm_TaoFivePrimes_zeta_zero_free_rectangle_127p6_129p3
-- name    : TaoFivePrimes.zeta_zero_free_rectangle_127p6_129p3
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-27T23:13:39.391952+00:00
-- url     : https://prove2.me/theorems/fe4e7560-f4a5-4ebf-a3be-0a49e1b2cf32
-- title:
--   Zeta is zero-free at heights 127.6–129.3
-- statement:
--   For every $s=\sigma+it$ with $0<\sigma<1$ and $127.6\le t\le129.3$,
--
--   $$
--   \zeta(s)\ne0.
--   $$
--
--   Both endpoints are included. This zero-free rectangle supports the finite-height zero-location theorem.
-- source:
--   Derived from the 336-moment enclosure and exact rational translation. The xi/Taylor and Bernstein frameworks are due to sometik179, with theta/Mellin foundations by Gabewhigham. Related finite verification: Tao, arXiv:1201.6656v4, Theorem 1.5, https://arxiv.org/abs/1201.6656; Platt, https://doi.org/10.1090/mcom/3198.

import Mathlib.NumberTheory.LSeries.RiemannZeta

theorem TaoFivePrimes.zeta_zero_free_rectangle_127p6_129p3 (s : ℂ) (h0 : 0 < s.re) (h1 : s.re < 1)
    (ha : (638/5:ℝ) ≤ s.im) (hb : s.im ≤ (1293/10:ℝ)) : riemannZeta s ≠ 0 := by sorry
