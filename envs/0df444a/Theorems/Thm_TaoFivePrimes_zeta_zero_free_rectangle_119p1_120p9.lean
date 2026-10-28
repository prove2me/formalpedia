-- Prove2me | Theorems.Thm_TaoFivePrimes_zeta_zero_free_rectangle_119p1_120p9
-- name    : TaoFivePrimes.zeta_zero_free_rectangle_119p1_120p9
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-27T20:34:16.37722+00:00
-- url     : https://prove2.me/theorems/81396532-e78c-46b2-98af-7328de77941e
-- title:
--   Zeta is zero-free in the critical strip at heights 119.1–120.9
-- statement:
--   For each $s=\sigma+it$ with $0<\sigma<1$ and $1191/10\le t\le1209/10$,
--
--   $$
--   \zeta(s)\ne0.
--   $$
--
--   Both endpoints are included. This zero-free rectangle is an input to the finite-height zero-location theorem used by the five-primes mission.
-- source:
--   Derived from 304 scaled Mellin-moment enclosures and the exact height-119 translation. The xi/Taylor and bivariate Bernstein frameworks are due to sometik179 (Prove2Me submissions c9908072-d99a-4431-aad8-a72c6352619a and f32249e2-6b1c-47ef-8195-015259f0d044); theta/Mellin foundations are due to Gabewhigham. Related finite verification: Tao, arXiv:1201.6656v4, Theorem 1.5, https://arxiv.org/abs/1201.6656.

import Mathlib.NumberTheory.LSeries.RiemannZeta

theorem TaoFivePrimes.zeta_zero_free_rectangle_119p1_120p9 (s : ℂ) (h0 : 0 < s.re) (h1 : s.re < 1)
    (ha : (1191/10:ℝ) ≤ s.im) (hb : s.im ≤ (1209/10:ℝ)) : riemannZeta s ≠ 0 := by sorry
