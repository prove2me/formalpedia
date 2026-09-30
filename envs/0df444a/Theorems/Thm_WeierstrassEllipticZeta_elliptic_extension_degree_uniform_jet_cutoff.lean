-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_elliptic_extension_degree_uniform_jet_cutoff
-- name    : WeierstrassEllipticZeta.elliptic_extension_degree_uniform_jet_cutoff
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-08T20:36:53.03343+00:00
-- url     : https://prove2.me/theorems/ff7f998a-094a-4cf8-ab08-c845dbb3f0c0
-- title:
--   A monotone degree-uniform cutoff for both polynomial chart jets
-- statement:
--   For complex parameters $g_2,g_3$, consider the two polynomial derivations on four-variable polynomial rings over $\mathbb C$:
--
--   $$\mathcal D_0=\partial_t+y\partial_x+(6x^2-g_2/2)\partial_y-x\partial_r$$
--
--   in variables $(t,x,y,r)$, and
--
--   $$\mathcal D_2=\partial_t+(-6b^2+g_2a^2/2)\partial_a
--   +(-1/2-g_2ab-3g_3a^2/2)\partial_b
--   +(-2g_2b^2-3g_3ab)\partial_d$$
--
--   in variables $(t,a,b,d)$.
--
--   For every fixed pair $g_2,g_3\in\mathbb C$, there is a nondecreasing function $B:\mathbb N\to\mathbb N$ with $B(d)>0$ for every $d$, such that for both charts, every polynomial $p\in\mathbb C[t,x,y,r]$ (respectively $\mathbb C[t,a,b,d]$) of total degree at most $e$, and every evaluation point $v\in\mathbb C^4$,
--
--   $$ (\mathcal D_c^kp)(v)=0\text{ for every }0\le k<B(e)
--   \quad\Longleftrightarrow\quad
--   (\mathcal D_c^kp)(v)=0\text{ for every }k\ge0.$$
--
--   The same cutoff function works for all polynomial coefficients, both charts and all evaluation points. It may depend on the fixed parameters $g_2,g_3$. The degree parameter is denoted $e$ here to distinguish it from the coordinate $d$ of the second chart. No cubic equation or nonzero denominator is required at the evaluation point; this is a theorem about polynomial derivations on the ambient affine coordinate rings.
--
--   The proof introduces formal coefficient variables for a finite basis of the vector space of polynomials of bounded degree. The resulting universal jet polynomials lie in a polynomial ring with finitely many variables. Noetherian stabilization yields a cutoff before specializing either the coefficients or the evaluation point. Taking a maximum over both charts and all smaller degrees makes the cutoff function nondecreasing.
--
--   **Formalization Note** The result is qualitative: it supplies a finite function of degree without claiming an explicit growth rate. Zero polynomials and degree zero are included. In Lean, chart indices 0 and 1 denote the homogeneous-coordinate charts 0 and 2.
-- source:
--   Derived Noetherian family lemma for the differential polynomial-ring approach in Senthil Kumar K (2026), Appendix A, especially its introductory paragraphs and the elliptic-extension curve in Appendix A.2 between (A.3) and (A.4), https://doi.org/10.1017/S001309152610145X. The proof parameterizes bounded-degree polynomials by a finite linear basis and applies the Hilbert basis theorem to universal polynomial jets. This coefficient-uniform qualitative assertion is proved here and is not quoted as the source quantitative Theorem A.2. The pinned Mathlib supplies Module.Finite for MvPolynomial.restrictTotalDegree, Module.finBasis, polynomial-ring Noetherianity and monotone_stabilizes_iff_noetherian.

import Definitions.Def_WeierstrassEllipticZeta_ProjectiveChartCalculus
import Mathlib.Algebra.MvPolynomial.Degrees

open WeierstrassEllipticZeta MvPolynomial

theorem WeierstrassEllipticZeta.elliptic_extension_degree_uniform_jet_cutoff (g₂ g₃ : ℂ) :
    ∃ B : ℕ → ℕ, Monotone B ∧ (∀ d : ℕ, 0 < B d) ∧
      ∀ (d : ℕ) (c : Fin 2) (p : MvPolynomial (Fin 4) ℂ), p.totalDegree ≤ d →
        ∀ v : Fin 4 → ℂ,
          ((∀ k < B d, eval v ((extensionChartDerivation g₂ g₃ c)^[k] p) = 0) ↔
            ∀ k : ℕ, eval v ((extensionChartDerivation g₂ g₃ c)^[k] p) = 0) := by sorry
