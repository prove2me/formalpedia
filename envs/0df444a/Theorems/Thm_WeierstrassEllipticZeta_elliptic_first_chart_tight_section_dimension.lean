-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_elliptic_first_chart_tight_section_dimension
-- name    : WeierstrassEllipticZeta.elliptic_first_chart_tight_section_dimension
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-22T19:31:23.173078+00:00
-- url     : https://prove2.me/theorems/27f77796-cc61-4ab6-afad-bba5b25d103a
-- title:
--   Tighter elliptic section dimension: coefficient 30 reduced to 7
-- statement:
--   Let $L$ be a period pair, $m\ge0$ and $n\ge1$. Let $V_{m,n}$ be the complex vector space spanned by restrictions of bihomogeneous sections of bidegree $(m,n)$ to the first cubic Weierstrass chart. This space is finite dimensional and satisfies
--
--   $$(m+1)(n+1)^2\le\dim_{\mathbb C}V_{m,n},\qquad 2\dim_{\mathbb C}V_{m,n}\le7(m+1)n(n+1).$$
--
--   In particular,
--
--   $$\dim_{\mathbb C}V_{m,n}\le7(m+1)n^2.$$
--
--   This improves the previously proved uniform upper coefficient from $30$ to $7$, with no change of space or additional geometric assumptions. The lower bound is reused from the already-Proved section-growth theorem. The new upper bound is a count of a spanning family; it is not claimed to be the exact dimension. The separate geometric comparison between chart costs and section dimension remains unproved.
-- source:
--   Derived quantitative refinement of WeierstrassEllipticZeta.elliptic_first_chart_section_dimension, https://prove2.me/theorems/13b6bf3d-1364-403b-8b54-d9e68f950754. Existing normalization uses the cubic relation y^2=4*x^3-g2*x-g3 and substitutes (1,t;1,x,y,u,y*u+2*x^2). Retaining the fibre exponent c<=n and the coupled weight 2*a+3*b+c<=4*n, b<2, gives exactly (m+1)*sum(c=0..n)(4*n-c)=(7/2)*(m+1)*n*(n+1) spanning monomials for n>=1. Thus the previously Proved uniform coefficient 30 is replaced by 7. The lower bound (m+1)*(n+1)^2 is reused from the Proved section-growth theorem https://prove2.me/theorems/af52a388-2af4-4817-ace8-f041f281a3c2. Pinned arithmetic source: Finset.sum_range_id_mul_two, https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Algebra/BigOperators/Intervals.lean. Source context for the projective coordinates: Senthil Kumar K (2026), Appendix A.2, exponential mapping and the chart display preceding Lemma A.1, https://www.cambridge.org/core/journals/proceedings-of-the-edinburgh-mathematical-society/article/algebraic-independence-of-values-of-weierstrass-elliptic-and-zeta-functions/E91A8EEEB1F63536D95D1DE7D7DD47E2#app1. This sharper dimension estimate is derived here, not quoted as a theorem of that paper. Frontier https://prove2.me/theorems/2cdf9a4f-11a1-457e-a98e-81ce6ee0b5e8 is reduced to the actual section-dimension budget W_min*E_min<=C*dim V_(m,n). That budget implies the parent with constant 7*C; the checked converse retains the parent constant using the existing lower dimension bound. The global geometric comparison remains unproved, and the integer-search bound is unchanged.

import Definitions.Def_WeierstrassEllipticZeta_TightCubicSections
import Mathlib.Tactic

noncomputable section
open scoped Classical
open WeierstrassEllipticZeta MvPolynomial

theorem WeierstrassEllipticZeta.elliptic_first_chart_tight_section_dimension (L : PeriodPair) (m n : ℕ)
    (hn : 1 ≤ n) :
    Module.Finite ℂ (firstChartSectionSpace L m n) ∧
    (m + 1) * (n + 1) ^ 2 ≤ Module.finrank ℂ (firstChartSectionSpace L m n) ∧
    2 * Module.finrank ℂ (firstChartSectionSpace L m n) ≤
      7 * (m + 1) * n * (n + 1) ∧
    Module.finrank ℂ (firstChartSectionSpace L m n) ≤ 7 * (m + 1) * n ^ 2 := by sorry
