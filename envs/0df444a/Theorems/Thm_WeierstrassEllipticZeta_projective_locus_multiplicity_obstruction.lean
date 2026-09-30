-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_projective_locus_multiplicity_obstruction
-- name    : WeierstrassEllipticZeta.projective_locus_multiplicity_obstruction
-- status  : Open
-- author  : @tomasz
-- created : 2026-09-08T16:57:23.740333+00:00
-- url     : https://prove2.me/theorems/a03fa7b0-6f8a-4868-b9aa-70398f00ef78
-- title:
--   Multiplicity obstruction on the explicit elliptic-extension projective locus
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
--   Suppose $P:E_\eta\to Z_{g_2,g_3}$ has nonzero homogeneous coordinate vectors
--
--   $$P([(z,u)])=[S_0(z):S_1(z):S_2(z):S_3(z)+uS_0(z):S_4(z)+uS_2(z)]$$
--
--   for all $z,u\in\mathbb C$. Write $r(z)$ for a chosen nonzero representative of the underlying projective point $P([(z,0)])$.
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
--   Here $p_a(t,[(z,u)])=t$, $p_E(t,[(z,u)])=z\bmod\Lambda$, and $q_H$ is the additive quotient map. Analytic orders take values in the extended natural numbers. The map is now known to take values in an explicit projective algebraic locus. Its identification with an algebraic-group embedding, the geometric multiplicity bound and subgroup projection profiles remain open obligations; neither surjectivity onto the whole locus nor finiteness of subgroup intersections is assumed.
-- source:
--   Senthil Kumar K (2026), Appendix A.2 exponential-map coordinates, Theorem A.2 and Lemma A.1(b), https://doi.org/10.1017/S001309152610145X. This inferred specialization is the existing descended-projective multiplicity obstruction with its map taking values in the quadratic-cubic locus forced by the explicit coordinates and DLMF 23.3.10. The separate complete lemma proves this factorization. Algebraic-group embedding, geometric multiplicity and subgroup profiles remain to be proved.

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

theorem WeierstrassEllipticZeta.projective_locus_multiplicity_obstruction
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
    (P : GraphQuotientExtension L.lattice η → ProjectiveExtensionLocus L.g₂ L.g₃)
    (hP : ∀ z u : ℂ, ∃ hv :
          ![S 0 z, S 1 z, S 2 z, S 3 z + u * S 0 z, S 4 z + u * S 2 z] ≠ 0,
        (P ((extensionPeriodGraph L.lattice η).mkQ (z, u))).val = Projectivization.mk ℂ
          ![S 0 z, S 1 z, S 2 z, S 3 z + u * S 0 z, S 4 z + u * S 2 z] hv) :
    ∃ C : ℝ, 0 < C ∧ ∀ m n U : ℕ,
      1 ≤ m → 1 ≤ n → 1 ≤ U → ∀ X : Finset ℂ,
      0 ∈ X → ∀ Q : MvPolynomial (Fin 7) ℂ,
        (∀ d ∈ Q.support, d 0 + d 1 = m ∧
          d 2 + d 3 + d 4 + d 5 + d 6 = n) →
        (fun z : ℂ => MvPolynomial.eval
          ![1, z, S 0 z, S 1 z, S 2 z, S 3 z, S 4 z] Q) ≠ 0 →
        (∀ v ∈ X + X + X, ∀ j : Fin 5,
          (P ((extensionCurve L.lattice η v).2)).val.rep j ≠ 0 →
          ((3 * U + 1 : ℕ) : ℕ∞) ≤ analyticOrderAt
            (fun z : ℂ => MvPolynomial.eval
              ![1, z,
                (P ((extensionCurve L.lattice η z).2)).val.rep 0 /
                  (P ((extensionCurve L.lattice η z).2)).val.rep j,
                (P ((extensionCurve L.lattice η z).2)).val.rep 1 /
                  (P ((extensionCurve L.lattice η z).2)).val.rep j,
                (P ((extensionCurve L.lattice η z).2)).val.rep 2 /
                  (P ((extensionCurve L.lattice η z).2)).val.rep j,
                (P ((extensionCurve L.lattice η z).2)).val.rep 3 /
                  (P ((extensionCurve L.lattice η z).2)).val.rep j,
                (P ((extensionCurve L.lattice η z).2)).val.rep 4 /
                  (P ((extensionCurve L.lattice η z).2)).val.rep j] Q) v) →
        ∃ H : Submodule ℤ (GraphExtensionGroup L.lattice η), ∃ a b : ℕ,
          ((a = 1 ∧ H ≤ LinearMap.ker (extensionAdditiveProjection L.lattice η)) ∨
            (a = 0 ∧ H ≤ LinearMap.ker (extensionEllipticProjection L.lattice η))) ∧
          b ≤ 2 ∧
          ((U + 1 : ℕ) : ℝ) *
            (H.mkQ '' (extensionCurve L.lattice η '' (X : Set ℂ))).ncard ≤
            C * (m : ℝ) ^ a * (n : ℝ) ^ b := by sorry
