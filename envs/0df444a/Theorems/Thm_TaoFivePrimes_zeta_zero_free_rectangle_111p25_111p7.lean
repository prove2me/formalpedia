-- Prove2me | Theorems.Thm_TaoFivePrimes_zeta_zero_free_rectangle_111p25_111p7
-- name    : TaoFivePrimes.zeta_zero_free_rectangle_111p25_111p7
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-27T19:29:17.360162+00:00
-- url     : https://prove2.me/theorems/5aabc074-52b6-497f-8c64-a5cc84930bf6
-- title:
--   Zeta is zero-free in the critical strip at heights 111.25–111.7
-- statement:
--   For every complex number $s=\sigma+it$ in the critical strip with $111.25\le t\le111.7$,
--
--   $$
--   \zeta(s)\ne0.
--   $$
--
--   Both endpoints are included. This zero-free rectangle is an input to the finite-height zero-location theorem in the five-primes mission.
-- source:
--   Derived from the 272-moment xi approximation centered at height 110.5, using the finite-height xi/Taylor and Bernstein methods of sometik179 (Prove2Me submissions c9908072-d99a-4431-aad8-a72c6352619a and f32249e2-6b1c-47ef-8195-015259f0d044), with theta/Mellin foundations by Gabewhigham. Related finite verification: Tao, arXiv:1201.6656v4, Theorem 1.5, https://arxiv.org/abs/1201.6656.

import Mathlib.NumberTheory.LSeries.RiemannZeta

theorem TaoFivePrimes.zeta_zero_free_rectangle_111p25_111p7 (s : ℂ) (h0 : 0 < s.re) (h1 : s.re < 1)
    (ha : (445/4:ℝ) ≤ s.im) (hb : s.im ≤ (1117/10:ℝ)) : riemannZeta s ≠ 0 := by sorry
