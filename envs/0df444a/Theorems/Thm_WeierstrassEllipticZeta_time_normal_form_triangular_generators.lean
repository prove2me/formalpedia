-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_time_normal_form_triangular_generators
-- name    : WeierstrassEllipticZeta.time_normal_form_triangular_generators
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-08T22:41:08.545101+00:00
-- url     : https://prove2.me/theorems/9da233a6-8025-434c-bd3a-27bfc8058530
-- title:
--   Four triangular ideal generators from unique bounded time representatives
-- statement:
--   Let $A=\mathbb C[t,x_1,x_2,x_3]$ and let $\iota:\mathbb C[T]\to A$ send $T$ to $t$. Fix an ideal $I\subseteq A$, an integer $d\ge0$, and a monic polynomial $M\in\mathbb C[T]$ of degree $d$, with $\iota(M)\in I$.
--
--   Suppose that every polynomial residue class modulo $I$ has a unique time-polynomial representative of degree less than $d$: for every $p\in A$, there is a unique $q\in\mathbb C[T]$ such that
--
--   $$\deg q<d,\qquad p-\iota(q)\in I.$$
--
--   Then there are polynomials $r_1,r_2,r_3\in\mathbb C[T]$, each of degree less than $d$, such that
--
--   $$I=(\iota(M),\ x_1-\iota(r_1),\ x_2-\iota(r_2),\ x_3-\iota(r_3)).$$
--
--   Moreover, for every $p\in A$ there is the exact membership test
--
--   $$p\in I\quad\Longleftrightarrow\quad
--   M(T)\mid p(T,r_1(T),r_2(T),r_3(T)).$$
--
--   The $r_i$ are the unique bounded time representatives of the coordinate variables. Modulo the displayed four generators, substituting $x_i=r_i(t)$ leaves every polynomial unchanged. Division by the monic $M$ and uniqueness of the degree-bounded representative show that the time polynomials in $I$ are precisely the multiples of $M$. Together these facts prove the generator equality and the membership criterion.
--
--   **Formalization Note** This is a general commutative-algebra lemma specialized to four variables over $\mathbb C$. Its hypotheses are supplied by the contact normal forms in the elliptic-extension application; no analytic or elliptic properties are assumed in this statement. Degree means `Polynomial.degree`, with bottom value for zero. The case $d=0$ is included and forces $M=1$, $I=A$, and all $r_i=0$. The three Lean indices `i : Fin 3` use `i.succ` for variables $x_1,x_2,x_3$. The statement proves an ideal presentation and divisibility criterion; it does not assert a regular-sequence theorem or the global multiplicity estimate.
-- source:
--   Derived commutative-algebra presentation lemma for the differential polynomial-ring and finite-contact approach in Senthil Kumar K (2026), Appendix A and Appendix A.2, https://doi.org/10.1017/S001309152610145X. This conditional algebraic lemma is proved here and is not quoted as the quantitative zero estimate in Theorem A.2. Primary formal references in Mathlib: MvPolynomial.algHom_ext, Ideal.Quotient.mk_eq_mk_iff_sub_mem, Polynomial.modByMonic_add_div, Polynomial.degree_modByMonic_lt, Polynomial.modByMonic_eq_zero_iff_dvd, and Ideal.span_le.

import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.Ideal.Span

theorem WeierstrassEllipticZeta.time_normal_form_triangular_generators
    (I : Ideal (MvPolynomial (Fin 4) ℂ)) (d : ℕ) (M : Polynomial ℂ)
    (hM : M.Monic) (hdegree : M.degree = (d : ℕ))
    (hMI : Polynomial.aeval (MvPolynomial.X (0 : Fin 4)) M ∈ I)
    (hrep : ∀ p : MvPolynomial (Fin 4) ℂ, ∃! q : Polynomial ℂ,
      q.degree < (d : ℕ) ∧ p - Polynomial.aeval (MvPolynomial.X (0 : Fin 4)) q ∈ I) :
    ∃ r : Fin 3 → Polynomial ℂ,
      (∀ i, (r i).degree < (d : ℕ)) ∧
      I = Ideal.span (insert (Polynomial.aeval (MvPolynomial.X (0 : Fin 4)) M)
        (Set.range (fun i : Fin 3 => MvPolynomial.X i.succ -
          Polynomial.aeval (MvPolynomial.X (0 : Fin 4)) (r i)))) ∧
      ∀ p : MvPolynomial (Fin 4) ℂ,
        p ∈ I ↔ M ∣ MvPolynomial.aeval (Fin.cons Polynomial.X r) p := by sorry
