-- Prove2me | Theorems.Thm_TaoFivePrimes_rh108p7to109_polynomial_negative
-- name    : TaoFivePrimes.rh108p7to109_polynomial_negative
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-27T18:48:10.460321+00:00
-- url     : https://prove2.me/theorems/45bf34ed-15ae-4bf8-aa2e-8d1514da1247
-- title:
--   Negative rounded xi polynomial on the 108.7–109 rectangle
-- statement:
--   Let $P$ be the rounded local xi polynomial centered at $\tfrac12+106.5i$ with the published height-$106.5$ coefficient list. Throughout the closed rectangle $0\le\sigma\le1$ and $108.7\le t\le109$,
--
--   $$
--   \operatorname{Re}P(\sigma+it)\le-140.
--   $$
--
--   This exact sign bound can be combined with an accurate xi approximation to exclude zeros in this part of the critical strip.
-- source:
--   Exact rational Bernstein certificate derived here from TaoFivePrimes_RH106To107RoundedCoefficients. Generic Bernstein method adapted from Prove2Me submission f32249e2-6b1c-47ef-8195-015259f0d044 by sometik179; original theta/Mellin foundations Gabewhigham. Related finite verification: Tao, arXiv:1201.6656v4, Theorem 1.5, https://arxiv.org/abs/1201.6656.

import Definitions.Def_TaoFivePrimes_RHLocalRoundedPolynomial
import Definitions.Def_TaoFivePrimes_RH106To107RoundedCoefficients

theorem TaoFivePrimes.rh108p7to109_polynomial_negative (s : ℂ) (h0 : 0 ≤ s.re) (h1 : s.re ≤ 1)
    (ha : (1087/10:ℝ) ≤ s.im) (hb : s.im ≤ 109) :
    (140:ℝ) ≤ -(TaoFivePrimes_RHLocalRoundedPolynomial
      TaoFivePrimes_RH106To107RoundedCoefficients 40 (213/2) s).re := by sorry
