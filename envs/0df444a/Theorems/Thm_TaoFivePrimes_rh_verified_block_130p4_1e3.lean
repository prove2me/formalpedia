-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_verified_block_130p4_1e3
-- name    : TaoFivePrimes.rh_verified_block_130p4_1e3
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-27T23:13:40.470325+00:00
-- url     : https://prove2.me/theorems/4b31a0b0-9556-4de2-b4b0-7bf15e566de2
-- title:
--   RH on the remaining slab from height 130.4 to 1000
-- statement:
--   Let $s=\sigma+it$ be a Riemann zeta zero with $0<\sigma<1$ and $130.4\le t\le1000$. Then
--
--   $$
--   \sigma=\tfrac12.
--   $$
--
--   Both endpoints are included; no simplicity assumption is made. This is the remaining finite-height block after the preceding slices.
-- source:
--   Derived from the 336-moment enclosure and exact rational translation. The xi/Taylor and Bernstein frameworks are due to sometik179, with theta/Mellin foundations by Gabewhigham. Related finite verification: Tao, arXiv:1201.6656v4, Theorem 1.5, https://arxiv.org/abs/1201.6656; Platt, https://doi.org/10.1090/mcom/3198.

import Mathlib.NumberTheory.LSeries.RiemannZeta

theorem TaoFivePrimes.rh_verified_block_130p4_1e3 (s : ℂ) (hs : riemannZeta s = 0)
    (h0 : 0 < s.re) (h1 : s.re < 1) (ha : (652/5:ℝ) ≤ s.im)
    (hb : s.im ≤ 10^3) : s.re = 1/2 := by sorry
