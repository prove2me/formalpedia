-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_elliptic_extension_projective_chart_normalization
-- name    : WeierstrassEllipticZeta.elliptic_extension_projective_chart_normalization
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-08T19:58:26.64067+00:00
-- url     : https://prove2.me/theorems/ea842355-2044-4d19-83b9-dfe3577c9019
-- title:
--   Bihomogeneous chart normalization, degree bounds and projective jets
-- statement:
--   Write a polynomial in seven variables as $Q(Y_0,Y_1;X_0,X_1,X_2,X_3,X_4)$. Define two algebra homomorphisms into four-variable polynomial rings over $\mathbb C$ by
--
--   $$N_0Q(t,x,y,r)=Q(1,t;1,x,y,r,yr+2x^2),$$
--
--   $$N_2Q(t,a,b,d)=Q(1,t;a,b,1,ad-2b^2,d).$$
--
--   These substitutions set the additive homogenizing coordinate to one and eliminate a projective coordinate using $X_0X_4-X_2X_3-2X_1^2=0$. The subscripts denote the nonzero homogeneous coordinate, so the Lean indices `0` and `1` select $N_0$ and $N_2$, respectively.
--
--   Let $g_2,g_3\in\mathbb C$, let the five functions $S_j:\mathbb C\to\mathbb C$ be entire, and let $R:\mathbb C\to Z^\circ_{g_2,g_3}$ take values in the projective locus
--
--   $$X_0X_4-X_2X_3-2X_1^2=0,\qquad
--   X_0X_2^2-4X_1^3+g_2X_0^2X_1+g_3X_0^3=0,$$
--
--   covered by $X_0\ne0$ or $X_2\ne0$. Assume $S(z)\ne0$ and $R(z)=[S_0(z):\cdots:S_4(z)]$ for every $z$. Denote a chosen nonzero representative of $R(z)$ by $r(z)$.
--
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
--   Assume the chart calculus already holds: for every four-variable polynomial $p$ and integer $k\ge0$, $\deg(\mathcal D_c^k p)\le\deg p+k$; on $U_c$, the $k$-th derivative of $p\circ f_c$ equals $(\mathcal D_c^kp)\circ f_c$, and order at least $k$ is equivalent to $(\mathcal D_c^lp)(f_c(z))=0$ for every $l<k$.
--
--   Then $r_j(z)\ne0$ if and only if $S_j(z)\ne0$ for every $z,j$. If $Q$ is bihomogeneous of bidegree $(m,n)$, with $m,n\ge0$, then for each chart and every $k\ge0$,
--
--   $$\deg(\mathcal D_c^kN_cQ)\le m+2n+k.$$
--
--   Here bihomogeneity means every supported monomial has exponent sum $m$ in $Y_0,Y_1$ and exponent sum $n$ in $X_0,\ldots,X_4$. At every $z\in U_c$, put
--
--   $$F_{c,Q}(w)=Q(1,w;r_0(w)/r_c(w),\ldots,r_4(w)/r_c(w)).$$
--
--   The exact identities are
--
--   $$F_{c,Q}^{(k)}(z)=(\mathcal D_c^kN_cQ)(f_c(z)),$$
--
--   $$k\le\operatorname{ord}_zF_{c,Q}
--   \quad\Longleftrightarrow\quad
--   (\mathcal D_c^lN_cQ)(f_c(z))=0\quad\text{for every }0\le l<k.$$
--
--   The assertion includes the zero polynomial, $k=0$, and infinite analytic order. All assertions about derivatives and orders are restricted to nonzero chart denominators. No regularity of the arbitrarily chosen projective representative is assumed: its ratios agree with the analytic $S$ ratios on these domains.
--
--   **Formalization Note** The proof works for arbitrary complex $g_2,g_3$; nonsingularity of the cubic is not needed for these normalization identities. Degree zero is used for the zero polynomial, following Mathlib.
-- source:
--   Derived normalization step for Senthil Kumar K (2026), Appendix A.2, the exponential-curve coordinates between (A.3) and (A.4), the bihomogeneous vanishing hypotheses of Theorem A.2 and the homogenization in (A.8)-(A.9), https://doi.org/10.1017/S001309152610145X. Eliminating a coordinate with the quadric gives the two displayed substitutions. The m+2n+k bound, representative-invariant germ comparison, and transport of the previously supplied chart jets are proved here; these exact specialized statements are not quoted from the source. Analytic order and derivative invariance under equality of germs use Mathlib analyticOrderAt_congr and Filter.EventuallyEq.iteratedDeriv_eq.

import Definitions.Def_WeierstrassEllipticZeta_ProjectiveChartNormalization
import Definitions.Def_WeierstrassEllipticZeta_ProjectiveExtensionChartLocus
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Algebra.MvPolynomial.Degrees

open WeierstrassEllipticZeta MvPolynomial

theorem WeierstrassEllipticZeta.elliptic_extension_projective_chart_normalization
    (g₂ g₃ : ℂ) (S : Fin 5 → ℂ → ℂ)
    (hS : ∀ j, AnalyticOnNhd ℂ (S j) Set.univ)
    (R : ℂ → ProjectiveExtensionChartLocus g₂ g₃)
    (hR : ∀ z : ℂ, ∃ hv : (fun j : Fin 5 => S j z) ≠ 0,
      (R z).val.val = Projectivization.mk ℂ (fun j => S j z) hv)
    (hjets : ∀ (c : Fin 2) (p : MvPolynomial (Fin 4) ℂ) (k : ℕ),
      ((extensionChartDerivation g₂ g₃ c)^[k] p).totalDegree ≤ p.totalDegree + k ∧
      ∀ z : ℂ, S (extensionChartDenominator c) z ≠ 0 →
        iteratedDeriv k (fun w => eval (extensionChartCoordinates S c w) p) z =
          eval (extensionChartCoordinates S c z) ((extensionChartDerivation g₂ g₃ c)^[k] p) ∧
        ((k : ℕ∞) ≤ analyticOrderAt
            (fun w => eval (extensionChartCoordinates S c w) p) z ↔
          ∀ l < k, eval (extensionChartCoordinates S c z)
            ((extensionChartDerivation g₂ g₃ c)^[l] p) = 0)) :
    (∀ (z : ℂ) (j : Fin 5), (R z).val.val.rep j ≠ 0 ↔ S j z ≠ 0) ∧
    ∀ (m n : ℕ) (Q : MvPolynomial (Fin 7) ℂ),
      (∀ d ∈ Q.support, d 0 + d 1 = m ∧
        d 2 + d 3 + d 4 + d 5 + d 6 = n) →
      ∀ (c : Fin 2) (k : ℕ),
        ((extensionChartDerivation g₂ g₃ c)^[k] (extensionChartNormalize c Q)).totalDegree ≤
          m + 2 * n + k ∧
        ∀ z : ℂ, S (extensionChartDenominator c) z ≠ 0 →
          iteratedDeriv k (fun w => eval
            ![1, w, (R w).val.val.rep 0 / (R w).val.val.rep (extensionChartDenominator c),
              (R w).val.val.rep 1 / (R w).val.val.rep (extensionChartDenominator c),
              (R w).val.val.rep 2 / (R w).val.val.rep (extensionChartDenominator c),
              (R w).val.val.rep 3 / (R w).val.val.rep (extensionChartDenominator c),
              (R w).val.val.rep 4 / (R w).val.val.rep (extensionChartDenominator c)] Q) z =
            eval (extensionChartCoordinates S c z)
              ((extensionChartDerivation g₂ g₃ c)^[k] (extensionChartNormalize c Q)) ∧
          ((k : ℕ∞) ≤ analyticOrderAt (fun w => eval
            ![1, w, (R w).val.val.rep 0 / (R w).val.val.rep (extensionChartDenominator c),
              (R w).val.val.rep 1 / (R w).val.val.rep (extensionChartDenominator c),
              (R w).val.val.rep 2 / (R w).val.val.rep (extensionChartDenominator c),
              (R w).val.val.rep 3 / (R w).val.val.rep (extensionChartDenominator c),
              (R w).val.val.rep 4 / (R w).val.val.rep (extensionChartDenominator c)] Q) z ↔
            ∀ l < k, eval (extensionChartCoordinates S c z)
              ((extensionChartDerivation g₂ g₃ c)^[l] (extensionChartNormalize c Q)) = 0) := by sorry
