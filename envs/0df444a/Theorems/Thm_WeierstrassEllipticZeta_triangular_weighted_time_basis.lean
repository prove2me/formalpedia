-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_triangular_weighted_time_basis
-- name    : WeierstrassEllipticZeta.triangular_weighted_time_basis
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-09T22:37:06.201601+00:00
-- url     : https://prove2.me/theorems/f793d2ce-d226-4c85-bf18-27507a4f24b3
-- title:
--   Explicit weighted time basis and coordinates of a finite quotient
-- statement:
--   Let $A=\mathbb C[x_0,x_1,x_2,x_3]$, let $I$ be an ideal of $A$, let $d\in\mathbb N$, and let $q\in A$. Write $E:\mathbb C[t]\to A$ for substitution of $x_0$ for $t$.
--
--   Suppose $T:A\to\mathbb C[t]$ is complex-linear and, for every $p\in A$, $T(p)$ is the unique polynomial of degree below $d$ satisfying
--   $$p-E(T(p))q\in I.$$
--   More explicitly, assume the degree bound and congruence for $T(p)$, and that every polynomial $b$ of degree below $d$ with $p-E(b)q\in I$ equals $T(p)$.
--
--   Then $A/I$ has a basis $\beta$ indexed by $0\leq i<d$ given by
--   $$\beta_i=[x_0^i q].$$
--   Each displayed polynomial representative has total degree at most $d-1+\deg_{\rm tot}q$. For every $p\in A$, the $i$th coordinate of $[p]$ in this basis is the coefficient of $t^i$ in $T(p)$. In particular,
--   $$[p]=\sum_{i=0}^{d-1}[t^i]T(p)\,[x_0^i q],\qquad
--   \dim_{\mathbb C}(A/I)=d.$$
--
--   Here brackets around a multivariate polynomial denote its residue class, and $[t^i]T(p)$ denotes a coefficient. Natural subtraction $d-1$ is truncated; polynomial degree at zero is $-\infty$. The case $d=0$ is included, with the empty basis of the zero quotient. No additional geometric hypotheses are implicit.
-- source:
--   Derived linear-algebra lemma for the finite-contact approach associated with Senthil Kumar K (2026), Appendix A and Theorem A.2, https://doi.org/10.1017/S001309152610145X. It is proved here under the explicit bounded linear division hypothesis, not quoted from that theorem. The quotient has basis given by the classes of x_0^i*q for i below d, with coordinates equal to coefficients of the bounded division result. Includes reconstruction, representative degree bounds and exact dimension d. Primary Mathlib references: LinearMap.codRestrict, quotKerEquivOfSurjective, Polynomial.degreeLT.basis, Module.Basis.map, sum_repr and Module.finrank_eq_card_basis. No Prove2Me theorem dependencies or new definitions.

import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Polynomial.DegreeLT

open scoped Classical

theorem WeierstrassEllipticZeta.triangular_weighted_time_basis
    (I : Ideal (MvPolynomial (Fin 4) ℂ)) (d : ℕ) (q : MvPolynomial (Fin 4) ℂ)
    (T : MvPolynomial (Fin 4) ℂ →ₗ[ℂ] Polynomial ℂ)
    (hrep : ∀ p : MvPolynomial (Fin 4) ℂ, (T p).degree < (d : ℕ) ∧
      p - Polynomial.aeval (MvPolynomial.X (0 : Fin 4)) (T p) * q ∈ I ∧
      ∀ b : Polynomial ℂ, b.degree < (d : ℕ) →
        p - Polynomial.aeval (MvPolynomial.X (0 : Fin 4)) b * q ∈ I → b = T p) :
    ∃ β : Module.Basis (Fin d) ℂ (MvPolynomial (Fin 4) ℂ ⧸ I),
      (∀ i : Fin d, β i = Ideal.Quotient.mk I ((MvPolynomial.X (0 : Fin 4)) ^ i.val * q) ∧
        ((MvPolynomial.X (0 : Fin 4)) ^ i.val * q).totalDegree ≤ d - 1 + q.totalDegree) ∧
      (∀ (p : MvPolynomial (Fin 4) ℂ) (i : Fin d),
        β.repr (Ideal.Quotient.mk I p) i = (T p).coeff i.val) ∧
      (∀ p : MvPolynomial (Fin 4) ℂ,
        Ideal.Quotient.mk I p = ∑ i : Fin d,
          (T p).coeff i.val • Ideal.Quotient.mk I ((MvPolynomial.X (0 : Fin 4)) ^ i.val * q)) ∧
      Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ I) = d := by sorry
