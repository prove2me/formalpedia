-- Prove2me | Theorems.Thm_TaoFivePrimes_rh118p5to119p1_imaginary_certificate
-- name    : TaoFivePrimes.rh118p5to119p1_imaginary_certificate
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-27T20:27:01.223771+00:00
-- url     : https://prove2.me/theorems/aed5d5e0-6126-4008-ad50-a08dbcf04481
-- title:
--   Polynomial imag certificate at heights 118.5–119.1
-- statement:
--   Let $P$ be the stored rounded local xi polynomial centered at $\tfrac12+119i$. For each $s=\sigma+it$ with $0\le\sigma\le1$ and $237/2\le t\le1191/10$,
--
--   $$
--   |\operatorname{Im}P(s)|\ge26|\sigma-\tfrac12|.
--   $$
--
--   This exact polynomial bound supports a finite-height zero-location argument when combined with a separate xi approximation.
-- source:
--   Derived from 304 scaled Mellin-moment enclosures and the exact height-119 translation. The xi/Taylor and bivariate Bernstein frameworks are due to sometik179 (Prove2Me submissions c9908072-d99a-4431-aad8-a72c6352619a and f32249e2-6b1c-47ef-8195-015259f0d044); theta/Mellin foundations are due to Gabewhigham. Related finite verification: Tao, arXiv:1201.6656v4, Theorem 1.5, https://arxiv.org/abs/1201.6656.

import Definitions.Def_TaoFivePrimes_RHLocalRationalPolynomial
import Definitions.Def_TaoFivePrimes_RH119RoundedCoefficients12

theorem TaoFivePrimes.rh118p5to119p1_imaginary_certificate (s : ℂ) (h0 : 0 ≤ s.re) (h1 : s.re ≤ 1)
    (ha : (237/2:ℝ) ≤ s.im) (hb : s.im ≤ (1191/10:ℝ)) :
    (26:ℝ)*|s.re-1/2| ≤
      |(TaoFivePrimes_RHLocalRationalPolynomial TaoFivePrimes_RH119RoundedCoefficients12 (10^12) 40 (238/2) s).im| := by sorry
