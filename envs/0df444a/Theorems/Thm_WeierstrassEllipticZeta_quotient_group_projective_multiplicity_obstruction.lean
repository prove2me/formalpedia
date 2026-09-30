-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_quotient_group_projective_multiplicity_obstruction
-- name    : WeierstrassEllipticZeta.quotient_group_projective_multiplicity_obstruction
-- status  : Open
-- author  : @tomasz
-- created : 2026-09-08T16:16:50.740096+00:00
-- url     : https://prove2.me/theorems/bc6b005b-cae1-48dd-9ed1-7a3f40d6b2b7
-- title:
--   Projective multiplicity obstruction on the explicit period quotient group
-- statement:
--   Let $L$ be a complex period pair with lattice $\Lambda$, normalized entire sigma differential data $\sigma$, and entire functions $S_0,\ldots,S_4$ having no common zero and satisfying
--
--   $$S(z)=\sigma(z)^3\big(1,\wp(z),\wp'(z),\zeta(z),\wp'(z)\zeta(z)+2\wp(z)^2\big)\qquad(z\notin\Lambda).$$
--
--   Let $\eta:\Lambda\to\mathbb C$ be a $\mathbb Z$-linear map equal to the canonical zeta quasiperiod at every lattice element. Use the quotient group and maps
--
--   $$G_\eta=\mathbb C\times\big(\mathbb C^2/\{(\omega,-\eta(\omega)):\omega\in\Lambda\}\big),$$
--
--   $$\varphi(z)=(z,[(z,0)]),\qquad p_a(t,[(z,u)])=t,\qquad
--   p_E(t,[(z,u)])=z\bmod\Lambda.$$
--
--   There is a real constant $C>0$, uniform in the following inputs. Let $m,n,U\ge1$ be integers, $X\subset\mathbb C$ finite with $0\in X$, and $Q$ a complex bihomogeneous polynomial of bidegree $(m,n)$ in two additive and five elliptic projective coordinates. Suppose its entire evaluation $F(z)=Q(1,z;S_0(z),\ldots,S_4(z))$ is not identically zero. Suppose that at every $v\in X+X+X$ and in every chart with $S_j(v)\ne0$, the evaluation
--
--   $$F_j(z)=Q\left(1,z;\frac{S_0(z)}{S_j(z)},\ldots,\frac{S_4(z)}{S_j(z)}\right)$$
--
--   has vanishing order at least $3U+1$ at $v$. Then there are an additive subgroup $H\subseteq G_\eta$ and nonnegative integers $a,b$ with $b\le2$, such that either $a=1$ and $H\subseteq\ker p_a$, or $a=0$ and $H\subseteq\ker p_E$, and
--
--   $$(U+1)|q_H(\varphi(X))|\le Cm^an^b.$$
--
--   Here orders are extended natural numbers and $q_H$ is the additive quotient map. This is the remaining geometric obstruction for the concrete period quotient: identification with the projective algebraic group, the multiplicity bound and the subgroup projection profiles remain to be proved. The complete quotient-geometry theorem supplies the canonical $\eta$ and transfers its conclusion to the parameter subgroup $K=\varphi^{-1}(H)$.
-- source:
--   Senthil Kumar K (2026), Appendix A.2 exponential-map description, Theorem A.2 and Lemma A.1(b), https://doi.org/10.1017/S001309152610145X. This inferred specialization states the geometric multiplicity obstruction in the explicit additive period quotient model, before pulling the subgroup back to the parameter line. The two projection-kernel profiles encode consequences of the algebraic subgroup classification. Identifying the quotient model and its chart curve with the algebraic group, proving the multiplicity estimate and proving those profiles remain obligations. Infinite discrete subgroup pullbacks are permitted.

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

theorem WeierstrassEllipticZeta.quotient_group_projective_multiplicity_obstruction
    (L : PeriodPair) (D : EllipticSigmaDifferentialData L)
    (S : Fin 5 → ℂ → ℂ)
    (hS : ∀ j, AnalyticOnNhd ℂ (S j) Set.univ)
    (hS_value : ∀ z : ℂ, z ∉ L.lattice → ∀ j : Fin 5,
      S j z = D.sigma z ^ 3 * ![1, L.weierstrassP z, L.derivWeierstrassP z,
        weierstrassZeta L z,
        L.derivWeierstrassP z * weierstrassZeta L z + 2 * L.weierstrassP z ^ 2] j)
    (hS_ne : ∀ z : ℂ, ∃ j : Fin 5, S j z ≠ 0)
    (η : L.lattice →ₗ[ℤ] ℂ)
    (hη : ∀ ω : L.lattice, η ω = zetaQuasiPeriod L ω) :
    ∃ C : ℝ, 0 < C ∧ ∀ m n U : ℕ,
      1 ≤ m → 1 ≤ n → 1 ≤ U → ∀ X : Finset ℂ,
      0 ∈ X → ∀ Q : MvPolynomial (Fin 7) ℂ,
        (∀ d ∈ Q.support, d 0 + d 1 = m ∧
          d 2 + d 3 + d 4 + d 5 + d 6 = n) →
        (fun z : ℂ => MvPolynomial.eval
          ![1, z, S 0 z, S 1 z, S 2 z, S 3 z, S 4 z] Q) ≠ 0 →
        (∀ v ∈ X + X + X, ∀ j : Fin 5, S j v ≠ 0 →
          ((3 * U + 1 : ℕ) : ℕ∞) ≤ analyticOrderAt
            (fun z : ℂ => MvPolynomial.eval
              ![1, z, S 0 z / S j z, S 1 z / S j z,
                S 2 z / S j z, S 3 z / S j z, S 4 z / S j z] Q) v) →
        ∃ H : Submodule ℤ (GraphExtensionGroup L.lattice η), ∃ a b : ℕ,
          ((a = 1 ∧ H ≤ LinearMap.ker (extensionAdditiveProjection L.lattice η)) ∨
            (a = 0 ∧ H ≤ LinearMap.ker (extensionEllipticProjection L.lattice η))) ∧
          b ≤ 2 ∧
          ((U + 1 : ℕ) : ℝ) *
            (H.mkQ '' (extensionCurve L.lattice η '' (X : Set ℂ))).ncard ≤
            C * (m : ℝ) ^ a * (n : ℝ) ^ b := by sorry
