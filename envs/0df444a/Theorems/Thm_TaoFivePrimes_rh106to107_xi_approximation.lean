-- Prove2me | Theorems.Thm_TaoFivePrimes_rh106to107_xi_approximation
-- name    : TaoFivePrimes.rh106to107_xi_approximation
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-27T17:49:57.454982+00:00
-- url     : https://prove2.me/theorems/88b9d765-5c35-48d3-9ead-2c9a2c90276e
-- title:
--   Certified xi approximation on the disk centered at height 106.5
-- statement:
--   Let $\xi$ be the completed xi function and let $c=\tfrac12+106.5i$. Let $a_0,\ldots,a_{39}$ be the stored integer coefficients and put
--
--   $$
--   P(z)=\sum_{n=0}^{39}\frac{a_n}{10^8}\,[-i(z-c)]^n.
--   $$
--
--   For every complex $z$ with $|z-c|\le1$,
--
--   $$
--   |10^{35}\xi(z)-P(z)|\le1.
--   $$
--
--   The certified disk includes the entire critical-strip rectangle $106\le\operatorname{Im}z\le107$. The inequality provides a reusable local input for a zero-free rectangle certificate.
-- source:
--   Derived from the published certified Mellin moments, TaoFivePrimes.rh14to100_moments_enclosed, and the local xi/Taylor method in Prove2Me submission c64db120-69c7-4491-bac6-95122a310a7a. Existing moment and local method by sometik179, theta/Mellin foundations by Gabewhigham. The center 106.5 and explicit error 1 are derived here; they are not a verbatim quotation. Related source: Tao, arXiv:1201.6656v4, Theorem 1.5, https://arxiv.org/abs/1201.6656.

import Definitions.Def_TaoFivePrimes_RHLocalRoundedPolynomial
import Definitions.Def_TaoFivePrimes_RH106To107RoundedCoefficients

theorem TaoFivePrimes.rh106to107_xi_approximation (z : ℂ)
    (hz : ‖z-RH1000Analytic.CertifiedLocalXi.center (213/2)‖ ≤ 1) :
    ‖((10^35:ℕ):ℂ)*RH1000Analytic.CertifiedLocalXi.xi z-
      TaoFivePrimes_RHLocalRoundedPolynomial TaoFivePrimes_RH106To107RoundedCoefficients 40 (213/2) z‖ ≤ 1 := by sorry
