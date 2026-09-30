-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_finite_set_projective_multiplicity_obstruction
-- name    : WeierstrassEllipticZeta.finite_set_projective_multiplicity_obstruction
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-08T15:36:35.480521+00:00
-- url     : https://prove2.me/theorems/530d72b4-289b-4875-9b59-ce3f6fd17572
-- title:
--   High projective multiplicity produces a subgroup obstruction
-- statement:
--   Let $L$ be a complex period pair with lattice $\Lambda$, canonical functions $\wp,\wp',\zeta$, and normalized entire sigma differential data $\sigma$. Let $S_0,\ldots,S_4$ be entire functions with no common zero such that
--
--   $$S(z)=\sigma(z)^3\big(1,\wp(z),\wp'(z),\zeta(z),\wp'(z)\zeta(z)+2\wp(z)^2\big)\qquad(z\notin\Lambda).$$
--
--   There exists $C>0$, uniform in the following inputs, with this property. Let $m,n,U\ge1$ be integers, let $X\subset\mathbb C$ be finite with $0\in X$, and let $Q\in\mathbb C[Y_0,Y_1,X_0,\ldots,X_4]$ be bihomogeneous of bidegree $(m,n)$. Suppose
--
--   $$F(z)=Q(1,z;S_0(z),\ldots,S_4(z))$$
--
--   is not identically zero. Suppose also that for every $v\in X+X+X$ and every $j\in\{0,\ldots,4\}$ with $S_j(v)\ne0$, the analytic chart evaluation
--
--   $$F_j(z)=Q\left(1,z;\frac{S_0(z)}{S_j(z)},\ldots,\frac{S_4(z)}{S_j(z)}\right)$$
--
--   has vanishing order at least $3U+1$ at $v$. Then there exist an additive subgroup $K\subset\mathbb C$ and nonnegative integers $a,b$ such that $b\le2$, either $a=1$ and $K=\{0\}$ or $a=0$ and $K\subseteq\Lambda$, and
--
--   $$(U+1)|q_K(X)|\le Cm^an^b,$$
--
--   where $q_K:\mathbb C\to\mathbb C/K$ is the additive quotient map. Vanishing order is an extended natural number, including infinity for a zero germ.
--
--   The subgroup $K$ represents the inverse image of a proper algebraic subgroup under the one-parameter group map. Establishing the existence of this obstruction, its two possible profiles, and the displayed multiplicity bound remains the geometric proof obligation. The statement imposes no numerical size conditions on $X$ and does not assume that $K$ is finite.
-- source:
--   Senthil Kumar K (2026), Appendix Theorem A.2, the T>=3 part of Theorem A.3, and Lemma A.1(b), https://doi.org/10.1017/S001309152610145X. This is an inferred pullback form of the geometric obstruction theorem: K is the inverse image of a proper connected algebraic subgroup under phi; a and b are the two degree exponents. The first coordinate of phi yields K=0 when a=1, while the elliptic projection yields K contained in the period lattice when a=0. The algebraic-group construction, multiplicity theorem, subgroup profiles and quotient identification remain to be proved. No finiteness of the intersection with the one-parameter group is assumed.

import Mathlib.Analysis.Analytic.Order
import Definitions.Def_WeierstrassEllipticZeta_SigmaDifferential
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Data.Set.Card

open WeierstrassEllipticZeta
open scoped Pointwise

theorem WeierstrassEllipticZeta.finite_set_projective_multiplicity_obstruction
    (L : PeriodPair) (D : EllipticSigmaDifferentialData L)
    (S : Fin 5 → ℂ → ℂ)
    (hS : ∀ j, AnalyticOnNhd ℂ (S j) Set.univ)
    (hS_value : ∀ z : ℂ, z ∉ L.lattice → ∀ j : Fin 5,
      S j z = D.sigma z ^ 3 * ![1, L.weierstrassP z, L.derivWeierstrassP z,
        weierstrassZeta L z,
        L.derivWeierstrassP z * weierstrassZeta L z + 2 * L.weierstrassP z ^ 2] j)
    (hS_ne : ∀ z : ℂ, ∃ j : Fin 5, S j z ≠ 0) :
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
        ∃ K : Submodule ℤ ℂ, ∃ a b : ℕ,
          ((a = 1 ∧ K = ⊥) ∨ (a = 0 ∧ K ≤ L.lattice)) ∧ b ≤ 2 ∧
          ((U + 1 : ℕ) : ℝ) * (K.mkQ '' (X : Set ℂ)).ncard ≤
            C * (m : ℝ) ^ a * (n : ℝ) ^ b := by sorry
