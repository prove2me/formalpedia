-- Prove2me | Theorems.Thm_TaoFivePrimes_zeta_zero_free_rectangle_124p5_125p4
-- name    : TaoFivePrimes.zeta_zero_free_rectangle_124p5_125p4
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-27T22:40:57.825562+00:00
-- url     : https://prove2.me/theorems/2a2d0a1a-5a2d-4522-ad70-4f72693fee90
-- title:
--   Zeta is zero-free in the critical strip at heights 124.5–125.4
-- statement:
--   For every $s=\sigma+it$ with $0<\sigma<1$ and $124.5\le t\le125.4$,
--
--   $$
--   \zeta(s)\ne0.
--   $$
--
--   Both endpoints are included. This zero-free rectangle supports a finite-height zero-location theorem.
-- source:
--   Derived from a rigorous 320-moment xi approximation and exact rational Bernstein polynomial bounds. The xi/Taylor and Bernstein frameworks are due to sometik179, with theta/Mellin foundations by Gabewhigham. Related finite verification: Tao, arXiv:1201.6656v4, Theorem 1.5, https://arxiv.org/abs/1201.6656; Platt, https://doi.org/10.1090/mcom/3198.

import Mathlib.NumberTheory.LSeries.RiemannZeta

theorem TaoFivePrimes.zeta_zero_free_rectangle_124p5_125p4 (s : ℂ) (h0 : 0 < s.re) (h1 : s.re < 1)
    (ha : (249/2:ℝ) ≤ s.im) (hb : s.im ≤ (627/5:ℝ)) : riemannZeta s ≠ 0 := by sorry
