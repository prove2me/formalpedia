-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_elliptic_first_chart_birelation_dimension
-- name    : WeierstrassEllipticZeta.elliptic_first_chart_birelation_dimension
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-22T21:18:03.580424+00:00
-- url     : https://prove2.me/theorems/ac9f5642-e857-4961-979d-a491fd9b47eb
-- title:
--   Elliptic section dimension: two relations reduce coefficient 7 to 5
-- statement:
--   Let L be a complex period pair, and let V_{m,n} be the space of restrictions of bihomogeneous polynomials of bidegree (m,n) to the first Weierstrass chart. Thus the ambient coordinate ring is
--
--   $$\mathbb C[t,x,y,u]/(y^2-4x^3+g_2x+g_3),$$
--
--   and the restricted sections arise by substituting
--
--   $$(1,t;1,x,y,u,yu+2x^2).$$
--
--   For every integer m ≥ 0 and n ≥ 1, this space is finite-dimensional, and
--
--   $$\dim_{\mathbb C}V_{m,n}\le(m+1)(3n^2+2)\le5(m+1)n^2.$$
--
--   The proof uses both the cubic relation and the quadratic coordinate relation obtained by retaining w = yu+2x² as a generator. It constructs a spanning family of exactly (m+1)(3n²+2) elements. Linear independence of that family, and equality in the dimension bound, are not asserted.
--
--   This improves the previous uniform upper coefficient 7 to 5. It supplies a sharper section-space factor for the A.1 geometric comparison, but does not establish that comparison or a value of its uniform multiplicity constant.
-- source:
--   Derived section-dimension refinement for Senthil Kumar K (2026), Appendix A.2, the projective-coordinate display before Lemma A.1, https://www.cambridge.org/core/journals/proceedings-of-the-edinburgh-mathematical-society/article/algebraic-independence-of-values-of-weierstrass-elliptic-and-zeta-functions/E91A8EEEB1F63536D95D1DE7D7DD47E2#app1. The bound is derived here, not quoted from the paper. Retain w=y*u+2*x^2 and reduce with x^3=(y^2+g2*x+g3)/4 and y*u=w-2*x^2. Both reductions decrease weight 2*a+2*b+3*c on x^a*y^b*u^c*w^d without increasing total degree. The resulting monomials have a<=2 and b*c=0. Their exact index count is (m+1)*sum(a=0..min(2,n))(n-a+1)^2=(m+1)*(3*n^2+2) for n>=1. This gives the new uniform upper bound 5*(m+1)*n^2, replacing coefficient 7 in https://prove2.me/theorems/27f77796-cc61-4ab6-afad-bba5b25d103a. No linear independence or equality with the section dimension is asserted. The existing geometric comparison https://prove2.me/theorems/b36f983b-aa58-4642-a9a3-5a0d99c64458 therefore implies https://prove2.me/theorems/2cdf9a4f-11a1-457e-a98e-81ce6ee0b5e8 with constant 5*C instead of 7*C. No new Open theorem is introduced, and the global geometric comparison and integer-search bound are unchanged.

import Definitions.Def_WeierstrassEllipticZeta_FirstChartSections
open WeierstrassEllipticZeta

theorem WeierstrassEllipticZeta.elliptic_first_chart_birelation_dimension (L : PeriodPair) (m n : ℕ)
    (hn : 1 ≤ n) :
    Module.Finite ℂ (firstChartSectionSpace L m n) ∧
    Module.finrank ℂ (firstChartSectionSpace L m n) ≤ (m + 1) * (3 * n ^ 2 + 2) ∧
    Module.finrank ℂ (firstChartSectionSpace L m n) ≤ 5 * (m + 1) * n ^ 2 := by sorry
