-- Prove2me | Theorems.Thm_TaoFivePrimes_zeta_zero_free_rectangle_114p6_116
-- name    : TaoFivePrimes.zeta_zero_free_rectangle_114p6_116
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-27T19:57:01.804906+00:00
-- url     : https://prove2.me/theorems/ca1a0476-ad7d-4906-9c71-b0aaaf1540f8
-- title:
--   Zeta is zero-free in the critical strip at heights 114.6–116
-- statement:
--   For each $s=\sigma+it$ with $0<\sigma<1$ and $573/5\le t\le116$,
--
--   $$
--   \zeta(s)\ne0.
--   $$
--
--   Both endpoints are included. This zero-free rectangle is an input to the finite-height zero-location theorem used by the five-primes mission.
-- source:
--   Derived from 304 scaled Mellin-moment enclosures and the exact height-114.5 translation. The xi/Taylor and bivariate Bernstein frameworks are due to sometik179 (Prove2Me submissions c9908072-d99a-4431-aad8-a72c6352619a and f32249e2-6b1c-47ef-8195-015259f0d044); theta/Mellin foundations are due to Gabewhigham. Related finite verification: Tao, arXiv:1201.6656v4, Theorem 1.5, https://arxiv.org/abs/1201.6656.

import Mathlib.NumberTheory.LSeries.RiemannZeta

theorem TaoFivePrimes.zeta_zero_free_rectangle_114p6_116 (s : ℂ) (h0 : 0 < s.re) (h1 : s.re < 1)
    (ha : (573/5:ℝ) ≤ s.im) (hb : s.im ≤ (116:ℝ)) : riemannZeta s ≠ 0 := by sorry
