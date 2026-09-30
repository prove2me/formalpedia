-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_elliptic_first_chart_section_growth
-- name    : WeierstrassEllipticZeta.elliptic_first_chart_section_growth
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-21T14:22:45.376229+00:00
-- url     : https://prove2.me/theorems/af52a388-2af4-4817-ace8-f041f281a3c2
-- title:
--   Two-sided bidegree growth of elliptic chart sections
-- statement:
--   For the affine Weierstrass cubic chart, let V(m,n) be the complex vector space obtained by restricting the bihomogeneous sections of bidegree (m,n) to the chart coordinate ring. For every m,n>=0 this space is finite-dimensional and
--
--       (m+1)*(n+1)^2 <= dim_C V(m,n).
--
--   For n>=1, the already proved upper bound also gives
--
--       dim_C V(m,n) <= 30*(m+1)*n^2.
--
--   The new lower bound is proved by an independent family of (m+1)*(n+1)^2 normal monomials. Take t^a*x^b*y^epsilon*u^c with 0<=a<=m, epsilon in {0,1}, and b+c+epsilon<=n. These are restrictions of sections of the specified bidegree. No nonzero linear combination can be a multiple of the Weierstrass cubic: its y-degree is at most one, whereas every nonzero multiple of the cubic has y-degree at least two.
--
--   The theorem establishes matching linear and quadratic growth in the two degrees, with explicit constants. The upper constant 30 is reused unchanged. No exact dimension formula, global multiplicity estimate, or A.1 completion is asserted.
-- source:
--   Two-sided section-dimension growth for the first Weierstrass cubic chart. This is an elementary supporting calculation for the section/Hilbert-function framework of Philippon (1986), section 3, especially Lemma 3.4, https://www.numdam.org/item/10.24033/bsmf.2060.pdf. It is not a claimed proof of the multihomogeneous Hilbert polynomial or the global multiplicity theorem. The new lower bound constructs (m+1)*(n+1)^2 independent sections from t^a*x^b*y^epsilon*u^c with epsilon<=1 and b+c+epsilon<=n. Monicity of the cubic in y, via degree additivity, proves their independence in the quotient. The upper bound 30*(m+1)*n^2 is reused unchanged from the proved section-dimension theorem. Together they replace the section-dimension budget by an equivalent explicit (r+1)*n^2 budget, preserving witnesses and changing the converse constant from C to 30*C. The A.1 cost bound itself remains open.

import Definitions.Def_WeierstrassEllipticZeta_FirstChartSections

open WeierstrassEllipticZeta

theorem WeierstrassEllipticZeta.elliptic_first_chart_section_growth (L : PeriodPair) (m n : ℕ) :
    Module.Finite ℂ (firstChartSectionSpace L m n) ∧
    (m + 1) * (n + 1) ^ 2 ≤ Module.finrank ℂ (firstChartSectionSpace L m n) ∧
    (1 ≤ n → Module.finrank ℂ (firstChartSectionSpace L m n) ≤
      30 * (m + 1) * n ^ 2) := by sorry
