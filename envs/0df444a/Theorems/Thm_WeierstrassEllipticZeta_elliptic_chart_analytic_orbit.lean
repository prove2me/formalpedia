-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_elliptic_chart_analytic_orbit
-- name    : WeierstrassEllipticZeta.elliptic_chart_analytic_orbit
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-20T19:24:54.627809+00:00
-- url     : https://prove2.me/theorems/12a842d9-2516-43ab-84ac-29dd485bc8dc
-- title:
--   Analytic orbit realization in both Weierstrass charts
-- statement:
--   Fix a complex period pair $L$, its canonical Weierstrass functions, normalized entire sigma differential data $D$, and five entire functions $S_0,\ldots,S_4$ satisfying
--
--   $$
--   S(z)=\sigma(z)^3(1,\wp(z),\wp'(z),\zeta(z),\wp'(z)\zeta(z)+2\wp(z)^2)
--   \quad(z\notin\Lambda).
--   $$
--
--   Let $Q\in\mathbb C[Y_0,\ldots,Y_6]$ be homogeneous of degree $n$ in its last five variables, and assume its entire pullback
--
--   $$F(z)=Q(1,z,S_0(z),S_1(z),S_2(z),S_3(z),S_4(z))$$
--
--   is not identically zero. No homogeneity assumption on the first two variables is needed here.
--
--   There are two affine charts. The first has denominator $S_0$ and coordinates
--   $v_0(z)=(z,S_1/S_0,S_2/S_0,S_3/S_0)$; the second has denominator $S_2$ and coordinates
--   $v_1(z)=(z,S_0/S_2,S_1/S_2,S_4/S_2)$. Write $Q_c$ for the normalized polynomial obtained by the chart substitutions
--
--   $$
--   Q_0(t,x,y,u)=Q(1,t,1,x,y,u,yu+2x^2),
--   \qquad Q_1(t,a,b,h)=Q(1,t,a,b,1,ah-2b^2,h).
--   $$
--
--   For either chart $c$ and every point $z_0$ where its denominator is nonzero, there exists a $\mathbb Q$-algebra homomorphism
--
--   $$\Phi:\mathbb C[T,X_1,X_2,X_3]\longrightarrow(\mathbb C\to\mathbb C)$$
--
--   such that $\Phi(r)(z)=r(v_c(z))$ for every polynomial $r$ and every $z$. The target has pointwise operations. Ratios are interpreted as total complex division; the analytic assertions concern neighbourhoods where the denominator is nonzero.
--
--   For the previously defined polynomial chart derivation $\delta_c$, viewed as a $\mathbb Q$-derivation, the germs of $\Phi(\delta_c r)$ and $(\Phi r)'$ agree at $z_0$ for every $r$. Moreover, $\Phi(Q_c)$ is analytic at $z_0$ and has finite analytic vanishing order there.
--
--   **Formalization Note.** This realizes the orbit and nonzero-germ hypotheses used by the analytic-transversality theorem in the actual two Weierstrass charts. It uses the Proved chart-flow and chart-jet identities. The local-coordinate interpretation of vanishing order and the denominator-clearing argument follow the framework of [Philippon (1986), §2, pp. 357–358 and Proposition 4.3, pp. 373–374](https://www.numdam.org/item/10.24033/bsmf.2060.pdf). This is an auxiliary chart construction, not the global zero estimate or component-selection theorem.
-- source:
--   Philippon (1986), Lemmes de zeros dans les groupes algebriques commutatifs, Bull. Soc. Math. France 114, 355-383. Definition of analytic order in local projective coordinates, section 2, pp. 357-358; coordinate-independence argument in Proposition 4.3, pp. 373-374. https://www.numdam.org/item/10.24033/bsmf.2060.pdf. Senthil Kumar K (2026), Appendix A, Theorem A.2. https://doi.org/10.1017/S001309152610145X. Auxiliary realization in the two explicit Weierstrass charts: construct evaluation and germ-level differential compatibility, and deduce a nonzero analytic germ from the nonzero entire projective pullback. The proof reuses the Proved chart-flow and chart-jet theorems. Component and prime selection and the uniform total degree estimate remain open.

import Definitions.Def_WeierstrassEllipticZeta_ProjectiveChartNormalization
import Definitions.Def_WeierstrassEllipticZeta_SigmaDifferential
import Mathlib.Analysis.Analytic.Order
import Mathlib.Algebra.Algebra.Pi

open WeierstrassEllipticZeta MvPolynomial
open scoped Topology

theorem WeierstrassEllipticZeta.elliptic_chart_analytic_orbit
    (L : PeriodPair) (D : EllipticSigmaDifferentialData L)
    (S : Fin 5 → ℂ → ℂ)
    (hS : ∀ j, AnalyticOnNhd ℂ (S j) Set.univ)
    (hS_value : ∀ z : ℂ, z ∉ L.lattice → ∀ j : Fin 5,
      S j z = D.sigma z ^ 3 * ![1, L.weierstrassP z, L.derivWeierstrassP z,
        weierstrassZeta L z,
        L.derivWeierstrassP z * weierstrassZeta L z + 2 * L.weierstrassP z ^ 2] j)
    (Q : MvPolynomial (Fin 7) ℂ) (n : ℕ)
    (hQ : ∀ d ∈ Q.support, d 2 + d 3 + d 4 + d 5 + d 6 = n)
    (hne : (fun w : ℂ => eval
      ![1, w, S 0 w, S 1 w, S 2 w, S 3 w, S 4 w] Q) ≠ 0)
    (c : Fin 2) (z : ℂ) (hz : S (extensionChartDenominator c) z ≠ 0) :
    ∃ φ : MvPolynomial (Fin 4) ℂ →ₐ[ℚ] (ℂ → ℂ),
      (∀ r w, φ r w = eval (extensionChartCoordinates S c w) r) ∧
      (∀ r, φ ((extensionChartDerivation L.g₂ L.g₃ c).restrictScalars ℚ r)
        =ᶠ[𝓝 z] deriv (φ r)) ∧
      AnalyticAt ℂ (φ (extensionChartNormalize c Q)) z ∧
      analyticOrderAt (φ (extensionChartNormalize c Q)) z ≠ ⊤ := by sorry
