-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_triangular_bounded_modular_division
-- name    : WeierstrassEllipticZeta.triangular_bounded_modular_division
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-09T22:07:30.715234+00:00
-- url     : https://prove2.me/theorems/30c0a5d9-d77e-4f72-bf84-eca111849270
-- title:
--   Canonical bounded linear division modulo a triangular ideal
-- statement:
--   Let $A=\mathbb C[x_0,x_1,x_2,x_3]$, let $I$ be an ideal of $A$, let $M\in\mathbb C[t]$ be monic, and let $r_1,r_2,r_3\in\mathbb C[t]$. Write $d=\deg M$, let $\phi:A\to\mathbb C[t]$ substitute $(t,r_1,r_2,r_3)$ for the four variables, and let $E:\mathbb C[t]\to A$ substitute $x_0$ for $t$. Assume
--   $$p\in I\quad\Longleftrightarrow\quad M\mid\phi(p)$$
--   for every $p\in A$. Suppose $q,a\in A$ satisfy $1-aq\in I$.
--
--   There exists a complex-linear map $T:A\to\mathbb C[t]$ with the explicit formula
--   $$T(p)=\phi(pa)\bmod M.$$
--   For every $p\in A$ it satisfies
--   $$\deg T(p)<d,\qquad \deg_{\rm tot}E(T(p))\le d-1,\qquad p-E(T(p))q\in I,$$
--   and
--   $$\deg_{\rm tot}(p-E(T(p))q)\le
--   \max\{\deg_{\rm tot}p,\ d-1+\deg_{\rm tot}q\}.$$
--   For every polynomial $b$ of degree below $d$,
--   $$p-E(b)q\in I\quad\Longleftrightarrow\quad b=T(p).$$
--   Furthermore, $T(p)=0$ if and only if $p\in I$. The map $T$ is the unique complex-linear map for which every output has degree below $d$ and satisfies the displayed division congruence.
--
--   The modulus remainder is division by the monic polynomial $M$. Subtraction $d-1$ in natural-number bounds is truncated; polynomial degree at zero is $-\infty$ and multivariate total degree at zero is zero. The case $M=1$, and hence $I=A$, is included. The result applies under the explicit presentation and inverse-certificate hypotheses and does not assume additional contact geometry.
-- source:
--   Derived commutative-algebra lemma for the finite-contact approach associated with Senthil Kumar K (2026), Appendix A and Theorem A.2, https://doi.org/10.1017/S001309152610145X. It is proved here under explicit monic time-presentation and inverse-certificate hypotheses, not quoted from that theorem. For each polynomial p it constructs the unique bounded time polynomial solving E(Tp)*q = p modulo I. The operator T is complex-linear, given explicitly by a monic remainder, has kernel I, and satisfies lift and residual degree bounds. Primary Mathlib references: Polynomial.add_modByMonic, smul_modByMonic, degree_modByMonic_lt, eq_zero_of_dvd_of_degree_lt and MvPolynomial total-degree bounds. No Prove2Me theorem dependencies or new definitions.

import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.Polynomial.Degree.Domain
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.Ideal.Operations

open scoped Classical

theorem WeierstrassEllipticZeta.triangular_bounded_modular_division
    (I : Ideal (MvPolynomial (Fin 4) ℂ)) (M : Polynomial ℂ)
    (hM : M.Monic) (r : Fin 3 → Polynomial ℂ)
    (hmem : ∀ p : MvPolynomial (Fin 4) ℂ,
      p ∈ I ↔ M ∣ MvPolynomial.aeval (Fin.cons Polynomial.X r) p)
    (q a : MvPolynomial (Fin 4) ℂ) (ha : 1 - a * q ∈ I) :
    ∃ T : MvPolynomial (Fin 4) ℂ →ₗ[ℂ] Polynomial ℂ,
      (∀ p : MvPolynomial (Fin 4) ℂ,
        T p = (MvPolynomial.aeval (Fin.cons Polynomial.X r) (p * a)) %ₘ M ∧
        (T p).degree < (M.natDegree : ℕ) ∧
        (Polynomial.aeval (MvPolynomial.X (R := ℂ) (0 : Fin 4)) (T p)).totalDegree ≤
          M.natDegree - 1 ∧
        p - Polynomial.aeval (MvPolynomial.X (0 : Fin 4)) (T p) * q ∈ I ∧
        (p - Polynomial.aeval (MvPolynomial.X (0 : Fin 4)) (T p) * q).totalDegree ≤
          max p.totalDegree (M.natDegree - 1 + q.totalDegree) ∧
        (∀ b : Polynomial ℂ, b.degree < (M.natDegree : ℕ) →
          (p - Polynomial.aeval (MvPolynomial.X (0 : Fin 4)) b * q ∈ I ↔ b = T p))) ∧
      (∀ p : MvPolynomial (Fin 4) ℂ, T p = 0 ↔ p ∈ I) ∧
      (∀ T' : MvPolynomial (Fin 4) ℂ →ₗ[ℂ] Polynomial ℂ,
        (∀ p : MvPolynomial (Fin 4) ℂ, (T' p).degree < (M.natDegree : ℕ) ∧
          p - Polynomial.aeval (MvPolynomial.X (0 : Fin 4)) (T' p) * q ∈ I) → T' = T) := by sorry
