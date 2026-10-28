-- Prove2me | Theorems.Thm_TaoFivePrimes_zeta_zero_free_rectangle_125p4_127p2
-- name    : TaoFivePrimes.zeta_zero_free_rectangle_125p4_127p2
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-27T22:49:54.933433+00:00
-- url     : https://prove2.me/theorems/6be46848-8524-47ea-843a-477f010ed5f4
-- title:
--   Zeta is zero-free in the critical strip at heights 125.4–127.2
-- statement:
--   For every $s=\sigma+it$ with $0<\sigma<1$ and $125.4\le t\le127.2$,
--
--   $$
--   \zeta(s)\ne0.
--   $$
--
--   Both endpoints are included. This zero-free rectangle supports a finite-height zero-location theorem.
-- source:
--   Derived from the proved 320-moment enclosure and exact rational translation. The xi/Taylor and Bernstein frameworks are due to sometik179, with theta/Mellin foundations by Gabewhigham. Related finite-height verification: Tao, arXiv:1201.6656v4, Theorem 1.5, https://arxiv.org/abs/1201.6656; Platt, https://doi.org/10.1090/mcom/3198.

import Mathlib.NumberTheory.LSeries.RiemannZeta

theorem TaoFivePrimes.zeta_zero_free_rectangle_125p4_127p2 (s : ℂ) (h0 : 0 < s.re) (h1 : s.re < 1)
    (ha : (627/5:ℝ) ≤ s.im) (hb : s.im ≤ (636/5:ℝ)) : riemannZeta s ≠ 0 := by sorry
