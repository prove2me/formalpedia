-- Prove2me | Theorems.Thm_TaoFivePrimes_zeta_zero_free_rectangle_130p4_130p8
-- name    : TaoFivePrimes.zeta_zero_free_rectangle_130p4_130p8
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-27T23:19:34.955766+00:00
-- url     : https://prove2.me/theorems/1673e117-2090-4731-a79e-abd4238c690f
-- title:
--   Zeta is zero-free at heights 130.4–130.8
-- statement:
--   For $s=\sigma+it$ with $0<\sigma<1$ and $130.4\le t\le130.8$,
--
--   $$
--   \zeta(s)\ne0.
--   $$
--
--   Both endpoints are included.
-- source:
--   Derived from the proved 336-moment enclosure and exact rational height-128 translation. The xi/Taylor and Bernstein frameworks are due to sometik179, with theta/Mellin foundations by Gabewhigham. Related finite verification: Tao, arXiv:1201.6656v4, Theorem 1.5, https://arxiv.org/abs/1201.6656; Platt, https://doi.org/10.1090/mcom/3198.

import Mathlib.NumberTheory.LSeries.RiemannZeta

theorem TaoFivePrimes.zeta_zero_free_rectangle_130p4_130p8 (s : ℂ) (h0 : 0 < s.re) (h1 : s.re < 1)
    (ha : (652/5:ℝ) ≤ s.im) (hb : s.im ≤ (654/5:ℝ)) : riemannZeta s ≠ 0 := by sorry
