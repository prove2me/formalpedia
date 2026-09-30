-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_equivariant_fiber_multiplicity_obstruction
-- name    : WeierstrassEllipticZeta.equivariant_fiber_multiplicity_obstruction
-- status  : Open
-- author  : @tomasz
-- created : 2026-09-08T17:51:39.924357+00:00
-- url     : https://prove2.me/theorems/faacd81c-84e4-4e3a-aab3-94305dd494e2
-- title:
--   Multiplicity obstruction for the equivariant additive-fiber model
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
--   Suppose $P:E_\eta\to Z^\circ_{g_2,g_3}$ has nonzero homogeneous coordinate vectors
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
--   There is a real constant $C>0$ uniform in integers $m,n,U\ge1$, finite sets $X\subset\mathbb C$ containing zero, and complex bihomogeneous polynomials $Q$ of bidegree $(m,n)$ in two additive and five projective coordinates. Assume
--
--   $$z\longmapsto Q(1,z;S_0(z),\ldots,S_4(z))\not\equiv0.$$
--
--   If, for every $v\in X+X+X$ and $j$ with $r_j(v)\ne0$, the function
--
--   $$z\longmapsto Q\left(1,z;\frac{r_0(z)}{r_j(z)},\ldots,\frac{r_4(z)}{r_j(z)}\right)$$
--
--   has analytic vanishing order at least $3U+1$ at $v$, then there are an additive subgroup $H\subseteq G_\eta$ and nonnegative integers $a,b$ with $b\le2$, such that either $a=1$ and $H\subseteq\ker p_a$, or $a=0$ and $H\subseteq\ker p_E$, and
--
--   $$(U+1)|q_H(\varphi(X))|\le Cm^an^b.$$
--
--   Here $p_a(t,[(z,u)])=t$, $p_E(t,[(z,u)])=z\bmod\Lambda$, and $q_H$ is the additive quotient map. Analytic orders take values in the extended natural numbers. The map takes values in the part of the explicit projective algebraic locus covered by the two standard affine charts with coordinate indices zero and two. The explicit additive action and its fibers are supplied, and the parametrization is equivariant. Identification with an algebraic-group embedding, the geometric multiplicity bound and subgroup projection profiles remain open obligations. Surjectivity of the cubic projection does not assume surjectivity of P; no finiteness of subgroup intersections is assumed.
-- source:
--   Senthil Kumar K (2026), Appendix A.2, exact sequence (A.3), exponential-map descriptions between (A.3) and (A.4), Theorem A.2 and Lemma A.1(b), https://doi.org/10.1017/S001309152610145X. This inferred specialization of the two-chart multiplicity frontier supplies the explicit pointwise additive-fiber model and equivariance of its parametrization. Algebraic-group identification, the geometric multiplicity bound and subgroup projection profiles remain obligations.

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

theorem WeierstrassEllipticZeta.equivariant_fiber_multiplicity_obstruction
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
    (P : GraphQuotientExtension L.lattice η → ProjectiveExtensionChartLocus L.g₂ L.g₃)
    (hP : ∀ z u : ℂ, ∃ hv :
          ![S 0 z, S 1 z, S 2 z, S 3 z + u * S 0 z, S 4 z + u * S 2 z] ≠ 0,
        (P ((extensionPeriodGraph L.lattice η).mkQ (z, u))).val.val = Projectivization.mk ℂ
          ![S 0 z, S 1 z, S 2 z, S 3 z + u * S 0 z, S 4 z + u * S 2 z] hv)
    (F : ProjectiveExtensionFiberModel L.g₂ L.g₃)
    (hP_action : ∀ (u : ℂ) (e : GraphQuotientExtension L.lattice η),
      P (e + extensionInclusion L.lattice η u) = F.action u (P e)) :
    ∃ C : ℝ, 0 < C ∧ ∀ m n U : ℕ,
      1 ≤ m → 1 ≤ n → 1 ≤ U → ∀ X : Finset ℂ,
      0 ∈ X → ∀ Q : MvPolynomial (Fin 7) ℂ,
        (∀ d ∈ Q.support, d 0 + d 1 = m ∧
          d 2 + d 3 + d 4 + d 5 + d 6 = n) →
        (fun z : ℂ => MvPolynomial.eval
          ![1, z, S 0 z, S 1 z, S 2 z, S 3 z, S 4 z] Q) ≠ 0 →
        (∀ v ∈ X + X + X, ∀ j : Fin 5,
          (P ((extensionCurve L.lattice η v).2)).val.val.rep j ≠ 0 →
          ((3 * U + 1 : ℕ) : ℕ∞) ≤ analyticOrderAt
            (fun z : ℂ => MvPolynomial.eval
              ![1, z,
                (P ((extensionCurve L.lattice η z).2)).val.val.rep 0 /
                  (P ((extensionCurve L.lattice η z).2)).val.val.rep j,
                (P ((extensionCurve L.lattice η z).2)).val.val.rep 1 /
                  (P ((extensionCurve L.lattice η z).2)).val.val.rep j,
                (P ((extensionCurve L.lattice η z).2)).val.val.rep 2 /
                  (P ((extensionCurve L.lattice η z).2)).val.val.rep j,
                (P ((extensionCurve L.lattice η z).2)).val.val.rep 3 /
                  (P ((extensionCurve L.lattice η z).2)).val.val.rep j,
                (P ((extensionCurve L.lattice η z).2)).val.val.rep 4 /
                  (P ((extensionCurve L.lattice η z).2)).val.val.rep j] Q) v) →
        ∃ H : Submodule ℤ (GraphExtensionGroup L.lattice η), ∃ a b : ℕ,
          ((a = 1 ∧ H ≤ LinearMap.ker (extensionAdditiveProjection L.lattice η)) ∨
            (a = 0 ∧ H ≤ LinearMap.ker (extensionEllipticProjection L.lattice η))) ∧
          b ≤ 2 ∧
          ((U + 1 : ℕ) : ℝ) *
            (H.mkQ '' (extensionCurve L.lattice η '' (X : Set ℂ))).ncard ≤
            C * (m : ℝ) ^ a * (n : ℝ) ^ b := by sorry
