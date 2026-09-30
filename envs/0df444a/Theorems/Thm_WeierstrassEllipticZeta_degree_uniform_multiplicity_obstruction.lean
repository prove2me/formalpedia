-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_degree_uniform_multiplicity_obstruction
-- name    : WeierstrassEllipticZeta.degree_uniform_multiplicity_obstruction
-- status  : Open
-- author  : @tomasz
-- created : 2026-09-08T20:36:58.383978+00:00
-- url     : https://prove2.me/theorems/e87ae2da-08c0-4225-b933-ab3a8d54233d
-- title:
--   Multiplicity obstruction with degree-uniform nonzero chart jets
-- statement:
--   Let $L$ be a complex period pair with lattice $\Lambda$, invariants $g_2,g_3$, normalized entire sigma differential data $\sigma$, and entire functions $S_0,\ldots,S_4$ without a common zero, satisfying
--
--   $$S(z)=\sigma(z)^3(1,\wp(z),\wp'(z),\zeta(z),\wp'(z)\zeta(z)+2\wp(z)^2)\quad(z\notin\Lambda).$$
--
--   Let $\eta:\Lambda\to\mathbb C$ be a $\mathbb Z$-linear map equal to the canonical quasiperiods. Put
--
--   $$E_\eta=\mathbb C^2/\{(\omega,-\eta(\omega)):\omega\in\Lambda\},\qquad
--   G_\eta=\mathbb C\times E_\eta,\qquad \varphi(z)=(z,[(z,0)]).$$
--
--   Let $Z_{g_2,g_3}\subseteq\mathbb P^4(\mathbb C)$ be the locus
--
--   $$X_0X_4-X_2X_3-2X_1^2=0,\qquad
--   X_0X_2^2-4X_1^3+g_2X_0^2X_1+g_3X_0^3=0.$$
--
--   Let
--
--   $$Z^\circ_{g_2,g_3}=\{[X]\in Z_{g_2,g_3}:X_0\ne0\ \text{or}\ X_2\ne0\}.$$
--
--   Suppose a bijection $P:E_\eta\simeq Z^\circ_{g_2,g_3}$ has nonzero homogeneous coordinate vectors
--
--   $$P([(z,u)])=[S_0(z):S_1(z):S_2(z):S_3(z)+uS_0(z):S_4(z)+uS_2(z)]$$
--
--   for all $z,u\in\mathbb C$. Assume also that $Z^\circ_{g_2,g_3}$ is equipped with a projective additive-fiber model $(\pi,A)$: the projection $\pi([X])=[X_0:X_1:X_2]$ has exactly the Weierstrass cubic as image, the action is
--
--   $$A(u,[X])=[X_0:X_1:X_2:X_3+uX_0:X_4+uX_2],$$
--
--   it obeys the additive action laws, and $\pi(p)=\pi(q)$ if and only if there is a unique $u$ with $A(u,p)=q$. Suppose $P$ respects the additive inclusion $i(u)=[(0,u)]$:
--
--   $$P(e+i(u))=A(u,P(e)).$$
--
--   Write $r(z)$ for a chosen nonzero representative of the underlying projective point $P([(z,0)])$.
--
--   Assume in addition the following polynomial differential equations for the normalized coordinate functions.
--
--   On the open set where $S_0\ne0$, put
--
--   $$x=\frac{S_1}{S_0},\qquad y=\frac{S_2}{S_0},\qquad t=\frac{S_3}{S_0}.$$
--
--   Then these functions have complex derivatives
--
--   $$x'=y,\qquad y'=6x^2-\frac{g_2}{2},\qquad t'=-x.$$
--
--   On the open set where $S_2\ne0$, put
--
--   $$a=\frac{S_0}{S_2},\qquad b=\frac{S_1}{S_2},\qquad d=\frac{S_4}{S_2}.$$
--
--   Their complex derivatives are
--
--   $$\begin{aligned}
--   a'&=-6b^2+\frac{g_2}{2}a^2,\\
--   b'&=-\frac12-g_2ab-\frac{3g_3}{2}a^2,\\
--   d'&=-2g_2b^2-3g_3ab.
--   \end{aligned}$$
--
--   Each assertion holds at every point where its specified denominator is nonzero, without excluding lattice points.
--
--   Assume also the following algebraic description of the chart jets.
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
--   Fix also a nondecreasing function $B:\mathbb N\to\mathbb N$ with positive values such that, for every degree bound $e$, chart $c$, polynomial $p$ of degree at most $e$, and point $v\in\mathbb C^4$, vanishing of $(\mathcal D_c^kp)(v)$ for all $k<B(e)$ is equivalent to vanishing for all $k\ge0$. This one cutoff function is fixed before the polynomial and finite-set parameters below.
--
--   There is a real constant $C>0$ uniform in integers $m,n,U\ge1$, finite sets $X\subset\mathbb C$ containing zero, and complex bihomogeneous polynomials $Q$ of bidegree $(m,n)$ in two additive and five projective coordinates. Assume that for every chart $c$ and point $z\in U_c$, some $k<B(m+2n)$ satisfies
--
--   $$ (\mathcal D_c^kN_cQ)(f_c(z))\ne0.$$
--
--   The bound uses the single degree-dependent function $B$, independently of the coefficients of $Q$. The normalized polynomials $N_cQ$ are defined as follows.
--
--   Write a polynomial in seven variables as $Q(Y_0,Y_1;X_0,X_1,X_2,X_3,X_4)$. Define two algebra homomorphisms into four-variable polynomial rings over $\mathbb C$ by
--
--   $$N_0Q(t,x,y,r)=Q(1,t;1,x,y,r,yr+2x^2),$$
--
--   $$N_2Q(t,a,b,d)=Q(1,t;a,b,1,ad-2b^2,d).$$
--
--   These substitutions set the additive homogenizing coordinate to one and eliminate a projective coordinate using $X_0X_4-X_2X_3-2X_1^2=0$. The subscripts denote the nonzero homogeneous coordinate, so the Lean indices `0` and `1` select $N_0$ and $N_2$, respectively.
--
--   Suppose for every $c\in\{0,2\}$ and $k\ge0$,
--
--   $$\deg(\mathcal D_c^kN_cQ)\le m+2n+k.$$
--
--   If for every $v\in X+X+X$, every chart $c$ with $S_c(v)\ne0$, and every $0\le k<3U+1$,
--
--   $$ (\mathcal D_c^kN_cQ)(f_c(v))=0,$$
--
--   then there are an additive subgroup $H\subseteq G_\eta$ and nonnegative integers $a,b$ with $b\le2$, such that either $a=1$ and $H\subseteq\ker p_a$, or $a=0$ and $H\subseteq\ker p_E$, and
--
--   $$(U+1)|q_H(\varphi(X))|\le Cm^an^b.$$
--
--   Here $p_a(t,[(z,u)])=t$, $p_E(t,[(z,u)])=z\bmod\Lambda$, and $q_H$ is the additive quotient map. The original analytic-order hypotheses have been converted into evaluations of explicitly normalized four-variable polynomials. The map takes values in the part of the explicit projective algebraic locus covered by the two standard affine charts with coordinate indices zero and two. The explicit additive action and its fibers are supplied, and the parametrization is bijective and equivariant, and its derivatives are supplied in both projective charts. Identification with an algebraic-group embedding, the geometric multiplicity bound and subgroup projection profiles remain open obligations. The supplied bijection is between the underlying sets; topological and algebraic compatibility remain to be proved. No finiteness of subgroup intersections is assumed.
-- source:
--   Inferred specialization of Senthil Kumar K (2026), Appendix A.2, Theorem A.2 and Lemma A.1(b), https://doi.org/10.1017/S001309152610145X. Supplies a proved monotone cutoff function for all polynomial chart jets of bounded degree and replaces the earlier per-polynomial finite-order certificate by nonzero jets below B(m+2n). The cutoff is fixed before the polynomial coefficients and evaluation points are chosen. The original geometric data, separate bidegrees, degree and vanishing conditions, positive-constant quantification, subgroup alternatives and numerical inequality are retained. Quantitative growth, algebraic-group identification and subgroup profiles remain Open.

import Definitions.Def_WeierstrassEllipticZeta_ProjectiveChartNormalization
import Definitions.Def_WeierstrassEllipticZeta_ProjectiveChartCalculus
import Definitions.Def_WeierstrassEllipticZeta_ProjectiveExtensionFiberModel
import Definitions.Def_WeierstrassEllipticZeta_ProjectiveExtensionChartLocus
import Definitions.Def_WeierstrassEllipticZeta_ProjectiveExtensionLocus
import Mathlib.LinearAlgebra.Projectivization.Basic
import Definitions.Def_TranscendenceTheory_GraphQuotientExtension
import Mathlib.Analysis.Analytic.Order
import Definitions.Def_WeierstrassEllipticZeta_SigmaDifferential
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Data.Set.Card

open WeierstrassEllipticZeta
open scoped Pointwise
open TranscendenceTheory

theorem WeierstrassEllipticZeta.degree_uniform_multiplicity_obstruction
    (L : PeriodPair) (D : EllipticSigmaDifferentialData L)
    (S : Fin 5 → ℂ → ℂ)
    (hS : ∀ j, AnalyticOnNhd ℂ (S j) Set.univ)
    (hS_value : ∀ z : ℂ, z ∉ L.lattice → ∀ j : Fin 5,
      S j z = D.sigma z ^ 3 * ![1, L.weierstrassP z, L.derivWeierstrassP z,
        weierstrassZeta L z,
        L.derivWeierstrassP z * weierstrassZeta L z + 2 * L.weierstrassP z ^ 2] j)
    (hS_ne : ∀ z : ℂ, ∃ j : Fin 5, S j z ≠ 0)
    (η : L.lattice →ₗ[ℤ] ℂ)
    (hη : ∀ ω : L.lattice, η ω = zetaQuasiPeriod L ω)
    (P : GraphQuotientExtension L.lattice η ≃ ProjectiveExtensionChartLocus L.g₂ L.g₃)
    (hP : ∀ z u : ℂ, ∃ hv :
          ![S 0 z, S 1 z, S 2 z, S 3 z + u * S 0 z, S 4 z + u * S 2 z] ≠ 0,
        (P ((extensionPeriodGraph L.lattice η).mkQ (z, u))).val.val = Projectivization.mk ℂ
          ![S 0 z, S 1 z, S 2 z, S 3 z + u * S 0 z, S 4 z + u * S 2 z] hv)
    (F : ProjectiveExtensionFiberModel L.g₂ L.g₃)
    (hP_action : ∀ (u : ℂ) (e : GraphQuotientExtension L.lattice η),
      P (e + extensionInclusion L.lattice η u) = F.action u (P e))
    (hflow :
    (∀ z : ℂ, S 0 z ≠ 0 →
      HasDerivAt (fun w => S 1 w / S 0 w) (S 2 z / S 0 z) z ∧
      HasDerivAt (fun w => S 2 w / S 0 w) (6 * (S 1 z / S 0 z) ^ 2 - L.g₂ / 2) z ∧
      HasDerivAt (fun w => S 3 w / S 0 w) (-S 1 z / S 0 z) z) ∧
    (∀ z : ℂ, S 2 z ≠ 0 →
      HasDerivAt (fun w => S 0 w / S 2 w)
        (-6 * (S 1 z / S 2 z) ^ 2 + L.g₂ / 2 * (S 0 z / S 2 z) ^ 2) z ∧
      HasDerivAt (fun w => S 1 w / S 2 w)
        (-(1 / 2 : ℂ) - L.g₂ * (S 0 z / S 2 z) * (S 1 z / S 2 z) -
          3 * L.g₃ / 2 * (S 0 z / S 2 z) ^ 2) z ∧
      HasDerivAt (fun w => S 4 w / S 2 w)
        (-2 * L.g₂ * (S 1 z / S 2 z) ^ 2 -
          3 * L.g₃ * (S 0 z / S 2 z) * (S 1 z / S 2 z)) z))
    (hjets :
    (∀ c : Fin 2, extensionChartDerivation L.g₂ L.g₃ c (extensionChartCubic L.g₂ L.g₃ c) = 0) ∧
    ∀ (c : Fin 2) (p : MvPolynomial (Fin 4) ℂ) (n : ℕ),
      ((extensionChartDerivation L.g₂ L.g₃ c)^[n] p).totalDegree ≤ p.totalDegree + n ∧
      ∀ z : ℂ, S (extensionChartDenominator c) z ≠ 0 →
        iteratedDeriv n (fun w => MvPolynomial.eval (extensionChartCoordinates S c w) p) z =
          MvPolynomial.eval (extensionChartCoordinates S c z)
            ((extensionChartDerivation L.g₂ L.g₃ c)^[n] p) ∧
        ((n : ℕ∞) ≤ analyticOrderAt
            (fun w => MvPolynomial.eval (extensionChartCoordinates S c w) p) z ↔
          ∀ k < n, MvPolynomial.eval (extensionChartCoordinates S c z)
            ((extensionChartDerivation L.g₂ L.g₃ c)^[k] p) = 0))
    (B : ℕ → ℕ)
    (hB : Monotone B ∧ (∀ d : ℕ, 0 < B d) ∧
      ∀ (d : ℕ) (c : Fin 2) (p : MvPolynomial (Fin 4) ℂ), p.totalDegree ≤ d →
        ∀ v : Fin 4 → ℂ,
          ((∀ k < B d, MvPolynomial.eval v ((extensionChartDerivation L.g₂ L.g₃ c)^[k] p) = 0) ↔
            ∀ k : ℕ, MvPolynomial.eval v ((extensionChartDerivation L.g₂ L.g₃ c)^[k] p) = 0)) :
    ∃ C : ℝ, 0 < C ∧ ∀ m n U : ℕ,
      1 ≤ m → 1 ≤ n → 1 ≤ U → ∀ X : Finset ℂ,
      0 ∈ X → ∀ Q : MvPolynomial (Fin 7) ℂ,
        (∀ d ∈ Q.support, d 0 + d 1 = m ∧
          d 2 + d 3 + d 4 + d 5 + d 6 = n) →
        (∀ (c : Fin 2) (z : ℂ), S (extensionChartDenominator c) z ≠ 0 →
          ∃ k < B (m + 2 * n), MvPolynomial.eval (extensionChartCoordinates S c z)
            ((extensionChartDerivation L.g₂ L.g₃ c)^[k] (extensionChartNormalize c Q)) ≠ 0) →
        (∀ (c : Fin 2) (k : ℕ),
          ((extensionChartDerivation L.g₂ L.g₃ c)^[k] (extensionChartNormalize c Q)).totalDegree ≤
            m + 2 * n + k) →
        (∀ v ∈ X + X + X, ∀ c : Fin 2,
          S (extensionChartDenominator c) v ≠ 0 →
          ∀ k < 3 * U + 1, MvPolynomial.eval (extensionChartCoordinates S c v)
            ((extensionChartDerivation L.g₂ L.g₃ c)^[k] (extensionChartNormalize c Q)) = 0) →
        ∃ H : Submodule ℤ (GraphExtensionGroup L.lattice η), ∃ a b : ℕ,
          ((a = 1 ∧ H ≤ LinearMap.ker (extensionAdditiveProjection L.lattice η)) ∨
            (a = 0 ∧ H ≤ LinearMap.ker (extensionEllipticProjection L.lattice η))) ∧
          b ≤ 2 ∧
          ((U + 1 : ℕ) : ℝ) *
            (H.mkQ '' (extensionCurve L.lattice η '' (X : Set ℂ))).ncard ≤
            C * (m : ℝ) ^ a * (n : ℝ) ^ b := by sorry
