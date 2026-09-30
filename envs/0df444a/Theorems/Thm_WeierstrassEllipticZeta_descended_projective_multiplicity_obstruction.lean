-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_descended_projective_multiplicity_obstruction
-- name    : WeierstrassEllipticZeta.descended_projective_multiplicity_obstruction
-- status  : Open
-- author  : @tomasz
-- created : 2026-09-08T16:38:12.879877+00:00
-- url     : https://prove2.me/theorems/36d2f08d-3098-4955-82d0-3641819e39d4
-- title:
--   Multiplicity obstruction in the descended elliptic-extension projective chart
-- statement:
--   Let $L$ have lattice $\Lambda$, normalized entire sigma differential data $\sigma$, and entire functions $S_0,\ldots,S_4$ without a common zero, whose values off $\Lambda$ are
--
--   $$S(z)=\sigma(z)^3(1,\wp(z),\wp'(z),\zeta(z),\wp'(z)\zeta(z)+2\wp(z)^2).$$
--
--   Let $\eta:\Lambda\to\mathbb C$ be a $\mathbb Z$-linear map equal to the canonical quasiperiods. Define $E_\eta=\mathbb C^2/\{(\omega,-\eta(\omega)):\omega\in\Lambda\}$, $G_\eta=\mathbb C\times E_\eta$, and $\varphi(z)=(z,[(z,0)])$. Suppose a map $P:E_\eta\to\mathbb P^4(\mathbb C)$ is given with nonzero homogeneous representatives
--
--   $$P([(z,u)])=[S_0(z):S_1(z):S_2(z):S_3(z)+uS_0(z):S_4(z)+uS_2(z)]$$
--
--   for all $z,u\in\mathbb C$. Write $r(z)$ for the nonzero representative chosen by Mathlib for $P([(z,0)])$.
--
--   There exists a real constant $C>0$, uniform in integers $m,n,U\ge1$, finite sets $X\subset\mathbb C$ containing zero, and complex bihomogeneous polynomials $Q$ of bidegree $(m,n)$ in two additive and five projective coordinates. Assume
--
--   $$F(z)=Q(1,z;S_0(z),\ldots,S_4(z))\not\equiv0,$$
--
--   and that for every $v\in X+X+X$ and $j$ with $r_j(v)\ne0$, the function
--
--   $$z\longmapsto Q\left(1,z;\frac{r_0(z)}{r_j(z)},\ldots,\frac{r_4(z)}{r_j(z)}\right)$$
--
--   has analytic vanishing order at least $3U+1$ at $v$. Then there exist an additive subgroup $H\subseteq G_\eta$ and nonnegative integers $a,b$ with $b\le2$, such that either $a=1$ and $H\subseteq\ker p_a$, or $a=0$ and $H\subseteq\ker p_E$, and
--
--   $$(U+1)|q_H(\varphi(X))|\le Cm^an^b.$$
--
--   Here $p_a(t,[(z,u)])=t$, $p_E(t,[(z,u)])=z\bmod\Lambda$, and $q_H$ is the additive quotient map. Vanishing orders take values in the extended natural numbers. This is the remaining multiplicity obstruction expressed in the descended projective chart. Identifying the map with an algebraic-group embedding, the geometric multiplicity theorem, and subgroup projection profiles remain to be proved. Discrete infinite subgroup intersections are allowed.
-- source:
--   Senthil Kumar K (2026), Appendix A.2 exponential-map description, Theorem A.2 and Lemma A.1(b), https://doi.org/10.1017/S001309152610145X. This inferred specialization expresses the existing quotient-group obstruction using normalized coordinates of its descended projective map. Projective descent is a separate complete lemma. Algebraic-group identification, the multiplicity estimate and subgroup profiles remain open; no finite-intersection assumption is added.

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

theorem WeierstrassEllipticZeta.descended_projective_multiplicity_obstruction
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
    (P : GraphQuotientExtension L.lattice η → Projectivization ℂ (Fin 5 → ℂ))
    (hP : ∀ z u : ℂ, ∃ hv :
          ![S 0 z, S 1 z, S 2 z, S 3 z + u * S 0 z, S 4 z + u * S 2 z] ≠ 0,
        P ((extensionPeriodGraph L.lattice η).mkQ (z, u)) = Projectivization.mk ℂ
          ![S 0 z, S 1 z, S 2 z, S 3 z + u * S 0 z, S 4 z + u * S 2 z] hv) :
    ∃ C : ℝ, 0 < C ∧ ∀ m n U : ℕ,
      1 ≤ m → 1 ≤ n → 1 ≤ U → ∀ X : Finset ℂ,
      0 ∈ X → ∀ Q : MvPolynomial (Fin 7) ℂ,
        (∀ d ∈ Q.support, d 0 + d 1 = m ∧
          d 2 + d 3 + d 4 + d 5 + d 6 = n) →
        (fun z : ℂ => MvPolynomial.eval
          ![1, z, S 0 z, S 1 z, S 2 z, S 3 z, S 4 z] Q) ≠ 0 →
        (∀ v ∈ X + X + X, ∀ j : Fin 5,
          (P ((extensionCurve L.lattice η v).2)).rep j ≠ 0 →
          ((3 * U + 1 : ℕ) : ℕ∞) ≤ analyticOrderAt
            (fun z : ℂ => MvPolynomial.eval
              ![1, z,
                (P ((extensionCurve L.lattice η z).2)).rep 0 /
                  (P ((extensionCurve L.lattice η z).2)).rep j,
                (P ((extensionCurve L.lattice η z).2)).rep 1 /
                  (P ((extensionCurve L.lattice η z).2)).rep j,
                (P ((extensionCurve L.lattice η z).2)).rep 2 /
                  (P ((extensionCurve L.lattice η z).2)).rep j,
                (P ((extensionCurve L.lattice η z).2)).rep 3 /
                  (P ((extensionCurve L.lattice η z).2)).rep j,
                (P ((extensionCurve L.lattice η z).2)).rep 4 /
                  (P ((extensionCurve L.lattice η z).2)).rep j] Q) v) →
        ∃ H : Submodule ℤ (GraphExtensionGroup L.lattice η), ∃ a b : ℕ,
          ((a = 1 ∧ H ≤ LinearMap.ker (extensionAdditiveProjection L.lattice η)) ∨
            (a = 0 ∧ H ≤ LinearMap.ker (extensionEllipticProjection L.lattice η))) ∧
          b ≤ 2 ∧
          ((U + 1 : ℕ) : ℝ) *
            (H.mkQ '' (extensionCurve L.lattice η '' (X : Set ℂ))).ncard ≤
            C * (m : ℝ) ^ a * (n : ℝ) ^ b := by sorry
