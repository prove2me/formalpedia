-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_finite_set_projective_zero_estimate
-- name    : WeierstrassEllipticZeta.finite_set_projective_zero_estimate
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-08T14:41:36.916433+00:00
-- url     : https://prove2.me/theorems/6b73b3ca-86dd-403b-aa73-7a11381f57c8
-- title:
--   Projective zero estimate from finite-set and lattice-quotient sizes
-- statement:
--   Let $L$ be a complex period pair with lattice $\Lambda$ and canonical functions $\wp,\wp',\zeta$. Let $\sigma$ be normalized entire sigma differential data, so $\sigma(0)=0$, $\sigma'(0)=1$, and $\sigma'=\zeta\sigma$ off $\Lambda$. Suppose $S_0,\ldots,S_4$ are entire, have no common zero, and satisfy
--
--   $$S(z)=\sigma(z)^3\big(1,\wp(z),\wp'(z),\zeta(z),\wp'(z)\zeta(z)+2\wp(z)^2\big)\qquad(z\notin\Lambda).$$
--
--   Write $\pi:\mathbb C\to\mathbb C/\Lambda$ for the additive quotient map. There is a real $C>0$ such that the following holds for all positive integers $m,n$, integers $T\ge3$, and finite sets $X\subset\mathbb C$ containing zero. Assume
--
--   $$3Cmn^2<T|X|,\qquad 3Cn^2<T|\pi(X)|.$$
--
--   For a polynomial $Q\in\mathbb C[Y_0,Y_1,X_0,X_1,X_2,X_3,X_4]$ bihomogeneous of bidegree $(m,n)$, define the entire function
--
--   $$H_Q(z)=Q\big(1,z;S_0(z),S_1(z),S_2(z),S_3(z),S_4(z)\big).$$
--
--   If $H_Q$ is not identically zero, there are $v\in X+X+X$ and an integer $0\le j\le T$ for which $H_Q^{(j)}(v)\ne0$.
--
--   The constant is uniform in $m,n,T,X,Q$. The finite set need not be a grid. The polynomial may depend on the fifth elliptic coordinate; every supported monomial must have total $Y$ degree exactly $m$ and total $X$ degree exactly $n$.
--
--   This is a sufficient finite-set form of the geometric zero estimate. The two size conditions account for proper subgroups whose first additive projection is zero and those whose projection is nonzero, respectively. Deducing it requires the algebraic-group multiplicity theorem, subgroup classification and the identification of local vanishing order with the entire lift. Those geometric assertions remain to be proved.
-- source:
--   Senthil Kumar K (2026), Appendix Theorem A.3, Lemma A.1(b), and Proposition A.1, https://doi.org/10.1017/S001309152610145X. This inferred sufficient version concerns arbitrary finite X in the analytic parameter, bidegree (m,n), and the two bounds 3C*m*n^2<T*|X| and 3C*n^2<T*|X mod Lambda|. For proper connected subgroups with zero first projection, quotient cardinality on phi(X) is |X| and r0-prime=1, r2-prime<=2. Otherwise subgroup classification implies containment in Ga times the additive kernel over E, so the quotient count is at least |X mod Lambda|, r0-prime=0 and r2-prime<=2. The multiplicity theorem, subgroup assertions and local lift interpretation remain proof obligations.

import Definitions.Def_WeierstrassEllipticZeta_SigmaDifferential
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Data.Set.Card

open WeierstrassEllipticZeta
open scoped Pointwise

theorem WeierstrassEllipticZeta.finite_set_projective_zero_estimate
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
        ∃ v ∈ X + X + X, ∃ j : ℕ, j ≤ T ∧ iteratedDeriv j
          (fun z : ℂ => MvPolynomial.eval
            ![1, z, S 0 z, S 1 z, S 2 z, S 3 z, S 4 z] Q) v ≠ 0 := by sorry
