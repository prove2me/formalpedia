-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_bounded_time_bezout_coefficients
-- name    : WeierstrassEllipticZeta.bounded_time_bezout_coefficients
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-09T00:28:55.503269+00:00
-- url     : https://prove2.me/theorems/35179790-08ab-4c48-95c3-5d56609435dd
-- title:
--   Bounded time coefficients and residual degrees for Bézout certificates
-- statement:
--   Let $A=\mathbb C[t,x_1,x_2,x_3]$, let $I\subseteq A$ be an ideal, and let $M\in\mathbb C[T]$ be monic of degree $d\in\mathbb N$. Fix $r_1,r_2,r_3\in\mathbb C[T]$ and set
--
--   $$\Phi(p)=p(T,r_1(T),r_2(T),r_3(T)),\qquad E(b)=b(t).$$
--
--   Assume the exact ideal-membership criterion
--
--   $$p\in I\quad\Longleftrightarrow\quad M\mid\Phi(p)\qquad(p\in A).$$
--
--   Suppose a finite family $f_0,\ldots,f_{K-1}\in A$ has coefficient polynomials $a_j\in A$ with
--
--   $$1-\sum_{j<K}a_jf_j\in I.$$
--
--   Then there exist univariate polynomials $b_j\in\mathbb C[T]$ such that, for every $j<K$,
--
--   $$\deg b_j<d,\qquad \operatorname{totaldeg}E(b_j)\le d\mathbin{\dot-}1,\qquad a_j-E(b_j)\in I,$$
--
--   and the reduced coefficients preserve the certificate:
--
--   $$R=1-\sum_{j<K}E(b_j)f_j\in I.$$
--
--   For any natural number $D$ bounding the total degree of every $f_j$, the residual also satisfies
--
--   $$\operatorname{totaldeg}R\le(d\mathbin{\dot-}1)+D.$$
--
--   Here $d\mathbin{\dot-}1=\max(d-1,0)$ is natural-number subtraction. One can take $b_j$ to be the remainder of $\Phi(a_j)$ on division by $M$.
--
--   **Formalization Note** The statement is conditional on the monic time presentation and an existing finite Bézout certificate. It imposes no degree bound on the original coefficients, the coordinate polynomials $r_i$, or the family $f_j$ except when invoking the final residual bound. It permits $K=0$ and $d=0$. For $d=0$, monicity gives $M=1$, all reduced coefficients are zero, and the membership criterion forces $I=A$. Lean's polynomial `degree` assigns bottom to zero, so the strict bound remains meaningful; multivariate `totalDegree` assigns zero to the zero polynomial, which explains the truncated subtraction. In the mission, $d$ is the contact length, so these bounds still depend on that length. They do not give the global zero estimate or a bound independent of the chosen contact data.
-- source:
--   Derived commutative-algebra coefficient reduction for the finite-contact approach associated with Senthil Kumar K (2026), Appendix A, https://doi.org/10.1017/S001309152610145X. Proved here under the explicit monic time-presentation and Bezout hypotheses; it is not quoted as Theorem A.2. Primary formal references: Mathlib Polynomial.degree_modByMonic_lt, modByMonic_eq_sub_mul_div, aeval_eq_sum_range, MvPolynomial.totalDegree_finsetSum_le, totalDegree_smul_le, totalDegree_X_pow, totalDegree_mul and totalDegree_add.

import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.Tactic.Ring

open scoped Classical

theorem WeierstrassEllipticZeta.bounded_time_bezout_coefficients
    (I : Ideal (MvPolynomial (Fin 4) ℂ)) (d : ℕ) (M : Polynomial ℂ)
    (hM : M.Monic) (hdegree : M.degree = (d : ℕ)) (r : Fin 3 → Polynomial ℂ)
    (hmem : ∀ p : MvPolynomial (Fin 4) ℂ,
      p ∈ I ↔ M ∣ MvPolynomial.aeval (Fin.cons Polynomial.X r) p)
    (K : ℕ) (f a : Fin K → MvPolynomial (Fin 4) ℂ)
    (ha : 1 - ∑ j : Fin K, a j * f j ∈ I) :
    ∃ b : Fin K → Polynomial ℂ,
      (∀ j : Fin K, (b j).degree < (d : ℕ) ∧
        (Polynomial.aeval (MvPolynomial.X (R := ℂ) (0 : Fin 4)) (b j)).totalDegree ≤ d - 1 ∧
        a j - Polynomial.aeval (MvPolynomial.X (0 : Fin 4)) (b j) ∈ I) ∧
      1 - ∑ j : Fin K,
        Polynomial.aeval (MvPolynomial.X (0 : Fin 4)) (b j) * f j ∈ I ∧
      ∀ D : ℕ, (∀ j : Fin K, (f j).totalDegree ≤ D) →
        (1 - ∑ j : Fin K,
          Polynomial.aeval (MvPolynomial.X (0 : Fin 4)) (b j) * f j).totalDegree ≤ d - 1 + D := by sorry
