-- Prove2me | Theorems.Thm_TaoFivePrimes_rh107to107p35_imaginary_certificate
-- name    : TaoFivePrimes.rh107to107p35_imaginary_certificate
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-27T17:57:13.388826+00:00
-- url     : https://prove2.me/theorems/a70692b5-1660-4305-b1ce-5fcae0813cfa
-- title:
--   Imaginary-part certificate for the critical-line slice 107–107.35
-- statement:
--   Let $P$ be the rounded local xi polynomial centered at $\tfrac12+106.5i$ with the published height-$106.5$ coefficients. For every $s=\sigma+it$ with $0\le\sigma\le1$ and $107\le t\le107.35$,
--
--   $$
--   |\operatorname{Im}P(s)|\ge200\left|\sigma-\tfrac12\right|.
--   $$
--
--   The linear factor reflects that $P$ is real on the critical line. The bound can be combined with a local analytic approximation to exclude zeros off that line in the indicated slice.
-- source:
--   New exact bivariate Bernstein certificate for the height-106.5 xi polynomial. Generic Bernstein method adapted from Prove2Me submission f32249e2-6b1c-47ef-8195-015259f0d044 by sometik179; the published Mellin moment data use theta/Mellin foundations by Gabewhigham. Related finite verification: Tao, arXiv:1201.6656v4, Theorem 1.5, https://arxiv.org/abs/1201.6656.

import Definitions.Def_TaoFivePrimes_RHLocalRoundedPolynomial
import Definitions.Def_TaoFivePrimes_RH106To107RoundedCoefficients

theorem TaoFivePrimes.rh107to107p35_imaginary_certificate (s : ℂ) (h0 : 0 ≤ s.re) (h1 : s.re ≤ 1)
    (ha : 107 ≤ s.im) (hb : s.im ≤ (2147/20:ℝ)) :
    (200:ℝ)*|s.re-1/2| ≤
      |(TaoFivePrimes_RHLocalRoundedPolynomial TaoFivePrimes_RH106To107RoundedCoefficients
        40 (213/2) s).im| := by sorry
