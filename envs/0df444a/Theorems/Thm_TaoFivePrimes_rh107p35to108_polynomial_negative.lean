-- Prove2me | Theorems.Thm_TaoFivePrimes_rh107p35to108_polynomial_negative
-- name    : TaoFivePrimes.rh107p35to108_polynomial_negative
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-27T18:06:16.659294+00:00
-- url     : https://prove2.me/theorems/e08cb7d7-d591-4e71-b4a7-fad807a4b4ce
-- title:
--   Negative rounded xi polynomial on the 107.35–108 rectangle
-- statement:
--   Let $P$ be the rounded local xi polynomial centered at $\tfrac12+106.5i$ with the published height-$106.5$ coefficient list. Then, throughout the closed rectangle $0\le\sigma\le1$ and $107.35\le t\le108$,
--
--   $$
--   \operatorname{Re}P(\sigma+it)\le-40.
--   $$
--
--   This exact polynomial inequality provides the sign margin for a zero-free rectangle beyond the first zero above height $106$.
-- source:
--   Exact rational Bernstein certificate derived here from TaoFivePrimes_RH106To107RoundedCoefficients. Generic Bernstein method adapted from Prove2Me submission f32249e2-6b1c-47ef-8195-015259f0d044 by sometik179; original theta/Mellin foundations Gabewhigham. Related numerical verification: Tao, arXiv:1201.6656v4, Theorem 1.5, https://arxiv.org/abs/1201.6656.

import Definitions.Def_TaoFivePrimes_RHLocalRoundedPolynomial
import Definitions.Def_TaoFivePrimes_RH106To107RoundedCoefficients

theorem TaoFivePrimes.rh107p35to108_polynomial_negative (s : ℂ) (h0 : 0 ≤ s.re) (h1 : s.re ≤ 1)
    (ha : (2147/20:ℝ) ≤ s.im) (hb : s.im ≤ 108) :
    (40:ℝ) ≤ -(TaoFivePrimes_RHLocalRoundedPolynomial
      TaoFivePrimes_RH106To107RoundedCoefficients 40 (213/2) s).re := by sorry
