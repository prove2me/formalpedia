-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_elliptic_chart_uniform_jet_cap
-- name    : WeierstrassEllipticZeta.elliptic_chart_uniform_jet_cap
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-20T23:42:26.55241+00:00
-- url     : https://prove2.me/theorems/4efb44c5-015a-452d-be72-481774157f26
-- title:
--   Degree-uniform exact ideal truncation in both Weierstrass charts
-- statement:
--   For every fixed period pair L, there exists a positive monotone function B from natural degrees to natural derivative orders. It works simultaneously for both Weierstrass charts and every auxiliary polynomial Q of any given bidegree (m,n).
--
--   Write d=m+2n and J_T=(F_c,Q_c,D_c Q_c,...,D_c^T Q_c), the chart ideal with the explicit cubic F_c and normalized polynomial Q_c. At every order T there is exact ideal equality
--
--   J_T = J_min(T,B(d)).
--
--   The displayed generators of the capped ideal have total degree at most max(3,d+B(d)). Their number is min(T,B(d))+2, hence at most B(d)+2. Both upper bounds are independent of T and of the coefficients of Q for fixed d and L. The theorem includes all natural m,n,T, including zero.
--
--   Earlier work supplied a degree-uniform cutoff for detecting common zeros of jets. The new conclusion is equality of ideals under every coefficient specialization, which also preserves nonreduced multiplicities and localized lengths. The existing individual jet-degree estimates are reused. The proof is non-effective: it supplies no numerical B(d) or growth bound in d. In particular it does not establish A.1's required C*m*n^2 or C*n^2 estimate.
-- source:
--   Supporting Noetherian specialization lemma for the A.1 formalization. Mathlib, RingTheory/Noetherian/Defs.lean, monotone_stabilizes_iff_noetherian: https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Noetherian/Defs.html#monotone_stabilizes_iff_noetherian. Universal coefficient variables make ideal stabilization uniform over all polynomials of bounded degree; specialization preserves exact ideal membership and yields J_T=J_min(T,B(m+2*n)) in both charts. B is positive and monotone, but no numerical value or growth bound is proved. Philippon (1986), Bull. Soc. Math. France 114, 355-383, section 5, pp. 380-382, https://www.numdam.org/item/10.24033/bsmf.2060.pdf, provides the broader derivative/translation-ideal framework. This is not that paper's quantitative zero estimate. Application: Senthil Kumar K (2026), Appendix A, Theorem A.2, https://doi.org/10.1017/S001309152610145X. The uniform A.1 degree budget and global geometric selection remain Open.

import Definitions.Def_WeierstrassEllipticZeta_CappedChartJets

open TranscendenceTheory WeierstrassEllipticZeta

theorem WeierstrassEllipticZeta.elliptic_chart_uniform_jet_cap (L : PeriodPair) :
    ∃ B : ℕ → ℕ, Monotone B ∧ (∀ d, 0 < B d) ∧
      ∀ (m n : ℕ) (Q : MvPolynomial (Fin 7) ℂ),
        (∀ d ∈ Q.support, d 0 + d 1 = m ∧ d 2 + d 3 + d 4 + d 5 + d 6 = n) →
        ∀ (c : Fin 2) (T : ℕ),
          extensionChartJetIdeal L Q c T =
            extensionChartJetIdeal L Q c (min T (B (m + 2 * n))) ∧
          ∀ j : Fin (min T (B (m + 2 * n)) + 2),
            (extensionChartJetGenerator L Q c (min T (B (m + 2 * n))) j).totalDegree ≤
              max 3 (m + 2 * n + B (m + 2 * n)) := by sorry
