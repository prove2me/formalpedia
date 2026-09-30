-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_finite_set_projective_chart_zero_estimate
-- name    : WeierstrassEllipticZeta.finite_set_projective_chart_zero_estimate
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-08T15:06:51.600262+00:00
-- url     : https://prove2.me/theorems/5db30691-b15b-406a-ad18-3a7a4e1be9aa
-- title:
--   Finite-set zero estimate in projective elliptic charts
-- statement:
--   Let $L$ be a complex period pair with lattice $\Lambda$ and canonical functions $\wp,\wp',\zeta$. Let $\sigma$ be normalized entire sigma differential data. Suppose the entire functions $S_0,\ldots,S_4$ have no common zero and satisfy
--
--   $$S(z)=\sigma(z)^3\big(1,\wp(z),\wp'(z),\zeta(z),\wp'(z)\zeta(z)+2\wp(z)^2\big)\qquad(z\notin\Lambda).$$
--
--   Let $\pi:\mathbb C\to\mathbb C/\Lambda$ be the additive quotient map. There exists $C>0$, uniform in the parameters below, such that for all integers $m,n\ge1$, $T\ge3$, and finite $X\subset\mathbb C$ with $0\in X$ and
--
--   $$3Cmn^2<T|X|,\qquad 3Cn^2<T|\pi(X)|,$$
--
--   the following holds. Let $Q\in\mathbb C[Y_0,Y_1,X_0,\ldots,X_4]$ be bihomogeneous of bidegree $(m,n)$, and suppose its entire evaluation
--
--   $$H_Q(z)=Q\big(1,z;S_0(z),\ldots,S_4(z)\big)$$
--
--   is not identically zero. There exist $v\in X+X+X$ and $j\in\{0,\ldots,4\}$ such that $S_j(v)\ne0$ and the local chart evaluation
--
--   $$H_{Q,j}(z)=Q\left(1,z;\frac{S_0(z)}{S_j(z)},\ldots,\frac{S_4(z)}{S_j(z)}\right)$$
--
--   has vanishing order at most $T$ at $v$. Its order is taken in $\mathbb N\cup\{\infty\}$; the nonzero denominator makes this function analytic on a neighborhood of $v$.
--
--   This is the remaining geometric zero estimate expressed in valid projective charts. The finite set and polynomial are arbitrary subject to the displayed hypotheses, and the polynomial may involve the fifth elliptic coordinate. The underlying algebraic-group construction, multiplicity theorem and subgroup analysis remain proof obligations.
-- source:
--   Senthil Kumar K (2026), Appendix Theorem A.3, Lemma A.1(b), and Proposition A.1, https://doi.org/10.1017/S001309152610145X. This inferred sufficient finite-set version uses the existing bounds 3C*m*n^2<T*|X| and 3C*n^2<T*|X mod Lambda| and expresses the conclusion as local vanishing order <=T in a chart with S_j(v) nonzero. The new complete chart-order lemma converts this condition to a nonzero derivative of the homogeneous entire lift. Constructing and identifying the algebraic-group curve, and proving the multiplicity theorem and subgroup facts, remain obligations.

import Mathlib.Analysis.Analytic.Order
import Definitions.Def_WeierstrassEllipticZeta_SigmaDifferential
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Data.Set.Card

open WeierstrassEllipticZeta
open scoped Pointwise

theorem WeierstrassEllipticZeta.finite_set_projective_chart_zero_estimate
    (L : PeriodPair) (D : EllipticSigmaDifferentialData L)
    (S : Fin 5 → ℂ → ℂ)
    (hS : ∀ j, AnalyticOnNhd ℂ (S j) Set.univ)
    (hS_value : ∀ z : ℂ, z ∉ L.lattice → ∀ j : Fin 5,
      S j z = D.sigma z ^ 3 * ![1, L.weierstrassP z, L.derivWeierstrassP z,
        weierstrassZeta L z,
        L.derivWeierstrassP z * weierstrassZeta L z + 2 * L.weierstrassP z ^ 2] j)
    (hS_ne : ∀ z : ℂ, ∃ j : Fin 5, S j z ≠ 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ m n T : ℕ,
      1 ≤ m → 1 ≤ n → 3 ≤ T → ∀ X : Finset ℂ,
      0 ∈ X →
      3 * C * (m : ℝ) * (n : ℝ) ^ 2 < (T : ℝ) * X.card →
      3 * C * (n : ℝ) ^ 2 <
        (T : ℝ) * (L.lattice.mkQ '' (X : Set ℂ)).ncard →
      ∀ Q : MvPolynomial (Fin 7) ℂ,
        (∀ d ∈ Q.support, d 0 + d 1 = m ∧
          d 2 + d 3 + d 4 + d 5 + d 6 = n) →
        (fun z : ℂ => MvPolynomial.eval
          ![1, z, S 0 z, S 1 z, S 2 z, S 3 z, S 4 z] Q) ≠ 0 →
        ∃ v ∈ X + X + X, ∃ j : Fin 5, S j v ≠ 0 ∧
          analyticOrderAt
            (fun z : ℂ => MvPolynomial.eval
              ![1, z, S 0 z / S j z, S 1 z / S j z,
                S 2 z / S j z, S 3 z / S j z, S 4 z / S j z] Q) v ≤ T := by sorry
