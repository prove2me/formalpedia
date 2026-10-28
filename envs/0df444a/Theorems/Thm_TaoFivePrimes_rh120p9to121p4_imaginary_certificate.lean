-- Prove2me | Theorems.Thm_TaoFivePrimes_rh120p9to121p4_imaginary_certificate
-- name    : TaoFivePrimes.rh120p9to121p4_imaginary_certificate
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-27T20:26:55.371624+00:00
-- url     : https://prove2.me/theorems/b4a27625-a31a-40d3-929c-574f52591caf
-- title:
--   Polynomial imag certificate at heights 120.9–121.4
-- statement:
--   Let $P$ be the stored rounded local xi polynomial centered at $\tfrac12+119i$. For each $s=\sigma+it$ with $0\le\sigma\le1$ and $1209/10\le t\le607/5$,
--
--   $$
--   |\operatorname{Im}P(s)|\ge3|\sigma-\tfrac12|.
--   $$
--
--   This exact polynomial bound supports a finite-height zero-location argument when combined with a separate xi approximation.
-- source:
--   Derived from 304 scaled Mellin-moment enclosures and the exact height-119 translation. The xi/Taylor and bivariate Bernstein frameworks are due to sometik179 (Prove2Me submissions c9908072-d99a-4431-aad8-a72c6352619a and f32249e2-6b1c-47ef-8195-015259f0d044); theta/Mellin foundations are due to Gabewhigham. Related finite verification: Tao, arXiv:1201.6656v4, Theorem 1.5, https://arxiv.org/abs/1201.6656.

import Definitions.Def_TaoFivePrimes_RHLocalRationalPolynomial
import Definitions.Def_TaoFivePrimes_RH119RoundedCoefficients12

theorem TaoFivePrimes.rh120p9to121p4_imaginary_certificate (s : ℂ) (h0 : 0 ≤ s.re) (h1 : s.re ≤ 1)
    (ha : (1209/10:ℝ) ≤ s.im) (hb : s.im ≤ (607/5:ℝ)) :
    (3:ℝ)*|s.re-1/2| ≤
      |(TaoFivePrimes_RHLocalRationalPolynomial TaoFivePrimes_RH119RoundedCoefficients12 (10^12) 40 (238/2) s).im| := by sorry
