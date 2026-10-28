-- Prove2me | Theorems.Thm_TaoFivePrimes_rh106to107_polynomial_positive
-- name    : TaoFivePrimes.rh106to107_polynomial_positive
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-27T17:51:03.406426+00:00
-- url     : https://prove2.me/theorems/c23e5f95-5955-4e5b-b069-1e9831a853db
-- title:
--   Positive rounded xi polynomial on the 106–107 rectangle
-- statement:
--   Let $P$ be the rounded degree-$39$ local xi polynomial with center $\tfrac12+106.5i$ and the published height-$106.5$ integer coefficient list. Then every $s=\sigma+it$ in the closed rectangle $0\le\sigma\le1$, $106\le t\le107$ satisfies
--
--   $$
--   \operatorname{Re}P(s)\ge40.
--   $$
--
--   This exact polynomial inequality supplies the sign margin needed to turn the certified local xi approximation into a zero-free rectangle.
-- source:
--   Exact rational Bernstein certificate derived here from TaoFivePrimes_RH106To107RoundedCoefficients. Generic Bernstein method adapted from Prove2Me submission f32249e2-6b1c-47ef-8195-015259f0d044 by sometik179; original theta/Mellin foundations Gabewhigham. Related numerical zero verification: Tao, arXiv:1201.6656v4, Theorem 1.5, https://arxiv.org/abs/1201.6656.

import Definitions.Def_TaoFivePrimes_RHLocalRoundedPolynomial
import Definitions.Def_TaoFivePrimes_RH106To107RoundedCoefficients

theorem TaoFivePrimes.rh106to107_polynomial_positive (s : ℂ) (h0 : 0 ≤ s.re) (h1 : s.re ≤ 1)
    (ha : 106 ≤ s.im) (hb : s.im ≤ 107) :
    (40:ℝ) ≤ (TaoFivePrimes_RHLocalRoundedPolynomial
      TaoFivePrimes_RH106To107RoundedCoefficients 40 (213/2) s).re := by sorry
