-- Prove2me | Theorems.Thm_TaoFivePrimes_zeta_zero_free_rectangle_129p8_130p4
-- name    : TaoFivePrimes.zeta_zero_free_rectangle_129p8_130p4
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-27T23:13:38.737582+00:00
-- url     : https://prove2.me/theorems/3a56c8cb-04a9-4382-8a3d-8b363c1d4896
-- title:
--   Zeta is zero-free at heights 129.8–130.4
-- statement:
--   For every $s=\sigma+it$ with $0<\sigma<1$ and $129.8\le t\le130.4$,
--
--   $$
--   \zeta(s)\ne0.
--   $$
--
--   Both endpoints are included. This zero-free rectangle supports the finite-height zero-location theorem.
-- source:
--   Derived from the 336-moment enclosure and exact rational translation. The xi/Taylor and Bernstein frameworks are due to sometik179, with theta/Mellin foundations by Gabewhigham. Related finite verification: Tao, arXiv:1201.6656v4, Theorem 1.5, https://arxiv.org/abs/1201.6656; Platt, https://doi.org/10.1090/mcom/3198.

import Mathlib.NumberTheory.LSeries.RiemannZeta

theorem TaoFivePrimes.zeta_zero_free_rectangle_129p8_130p4 (s : ℂ) (h0 : 0 < s.re) (h1 : s.re < 1)
    (ha : (649/5:ℝ) ≤ s.im) (hb : s.im ≤ (652/5:ℝ)) : riemannZeta s ≠ 0 := by sorry
