-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_elliptic_extension_projective_chart_jets
-- name    : WeierstrassEllipticZeta.elliptic_extension_projective_chart_jets
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-08T19:35:14.050561+00:00
-- url     : https://prove2.me/theorems/88879e09-66d6-4649-836d-74852b452bbc
-- title:
--   Polynomial chart jets, degree growth and analytic vanishing order
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
--   in variables $(t,a,b,d)$. Their respective cubic polynomials are
--
--   $$G_0=y^2-4x^3+g_2x+g_3,\qquad G_2=a-4b^3+g_2a^2b+g_3a^3.$$
--
--   Given five functions $S_j:\mathbb C\to\mathbb C$, the coordinate maps are
--
--   $$f_0(z)=(z,S_1/S_0,S_2/S_0,S_3/S_0)(z),\qquad
--   f_2(z)=(z,S_0/S_2,S_1/S_2,S_4/S_2)(z),$$
--
--   used on $U_0=\{S_0\ne0\}$ and $U_2=\{S_2\ne0\}$, respectively. These are the affine coordinates for the zero and second homogeneous-coordinate charts of the elliptic-extension model.
--
--   Assume each $S_j$ is entire and that, on its domain $U_c$, the coordinate map $f_c$ solves the displayed polynomial differential system: its coordinate derivatives equal the coefficients of $\mathcal D_c$ evaluated at $f_c(z)$.
--
--   For $c\in\{0,2\}$, the derivation annihilates its cubic:
--
--   $$\mathcal D_cG_c=0.$$
--
--   For every polynomial $p$ in the four coordinates and every integer $n\ge0$,
--
--   $$\deg(\mathcal D_c^n p)\le\deg(p)+n.$$
--
--   At each $z\in U_c$, the exact derivative identity is
--
--   $$\frac{d^n}{dz^n}\big(p(f_c(z))\big)=(\mathcal D_c^n p)(f_c(z)),$$
--
--   and the vanishing-order criterion is
--
--   $$n\le\operatorname{ord}_z(p\circ f_c)
--   \quad\Longleftrightarrow\quad
--   (\mathcal D_c^k p)(f_c(z))=0\quad\text{for all }0\le k<n.$$
--
--   The analytic order is allowed to be infinite. These statements include $n=0$ and the zero polynomial, using degree zero for the zero polynomial.
--
--   This supplies polynomial tests for all finite orders of vanishing in both projective charts, with controlled degree growth. No lattice point is excluded when its chart denominator is nonzero. The cubic identity permits differentiation modulo the cubic relation. The theorem concerns differential presentations and vanishing orders; the geometric multiplicity bound remains a separate obligation.
--
--   **Formalization Note** The two charts are indexed by `Fin 2`: index 0 denotes the $X_0$ chart and index 1 denotes the $X_2$ chart. Complex parameters are fixed coefficients, so they contribute zero to total degree.
-- source:
--   Derived from the polynomial differential equations of the one-parameter exponential curve in Senthil Kumar K (2026), Appendix A.2, the displays between (A.3) and (A.4), for the vanishing-along-the-curve hypotheses of Theorem A.2, https://doi.org/10.1017/S001309152610145X. The polynomial differentiation and degree argument generalizes the integer-coefficient platform theorem TranscendenceTheory.polynomial_ode_iterated_deriv (f33f6490-4860-4162-8a4e-3ab61a20213f), associated with Section 4, Lemma 4, equations (8)-(10), to complex coefficients. The exact vanishing criterion is Taylor theory, formalized by Mathlib natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero. The chart-specific all-order assertion and cubic-annihilation identities are derived here, not quoted as a theorem of the source.

import Definitions.Def_WeierstrassEllipticZeta_ProjectiveChartCalculus
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

open WeierstrassEllipticZeta

theorem WeierstrassEllipticZeta.elliptic_extension_projective_chart_jets
    (g₂ g₃ : ℂ) (S : Fin 5 → ℂ → ℂ)
    (hS : ∀ j, AnalyticOnNhd ℂ (S j) Set.univ)
    (hflow :
      (∀ z : ℂ, S 0 z ≠ 0 →
        HasDerivAt (fun w => S 1 w / S 0 w) (S 2 z / S 0 z) z ∧
        HasDerivAt (fun w => S 2 w / S 0 w) (6 * (S 1 z / S 0 z) ^ 2 - g₂ / 2) z ∧
        HasDerivAt (fun w => S 3 w / S 0 w) (-S 1 z / S 0 z) z) ∧
      (∀ z : ℂ, S 2 z ≠ 0 →
        HasDerivAt (fun w => S 0 w / S 2 w)
          (-6 * (S 1 z / S 2 z) ^ 2 + g₂ / 2 * (S 0 z / S 2 z) ^ 2) z ∧
        HasDerivAt (fun w => S 1 w / S 2 w)
          (-(1 / 2 : ℂ) - g₂ * (S 0 z / S 2 z) * (S 1 z / S 2 z) -
            3 * g₃ / 2 * (S 0 z / S 2 z) ^ 2) z ∧
        HasDerivAt (fun w => S 4 w / S 2 w)
          (-2 * g₂ * (S 1 z / S 2 z) ^ 2 -
            3 * g₃ * (S 0 z / S 2 z) * (S 1 z / S 2 z)) z)) :
    (∀ c : Fin 2, extensionChartDerivation g₂ g₃ c (extensionChartCubic g₂ g₃ c) = 0) ∧
    ∀ (c : Fin 2) (p : MvPolynomial (Fin 4) ℂ) (n : ℕ),
      ((extensionChartDerivation g₂ g₃ c)^[n] p).totalDegree ≤ p.totalDegree + n ∧
      ∀ z : ℂ, S (extensionChartDenominator c) z ≠ 0 →
        iteratedDeriv n (fun w => MvPolynomial.eval (extensionChartCoordinates S c w) p) z =
          MvPolynomial.eval (extensionChartCoordinates S c z)
            ((extensionChartDerivation g₂ g₃ c)^[n] p) ∧
        ((n : ℕ∞) ≤ analyticOrderAt
            (fun w => MvPolynomial.eval (extensionChartCoordinates S c w) p) z ↔
          ∀ k < n, MvPolynomial.eval (extensionChartCoordinates S c z)
            ((extensionChartDerivation g₂ g₃ c)^[k] p) = 0) := by sorry
