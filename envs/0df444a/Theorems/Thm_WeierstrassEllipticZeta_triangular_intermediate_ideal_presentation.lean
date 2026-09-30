-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_triangular_intermediate_ideal_presentation
-- name    : WeierstrassEllipticZeta.triangular_intermediate_ideal_presentation
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-09T12:37:42.348785+00:00
-- url     : https://prove2.me/theorems/2a175f47-e267-43d8-830d-14765902aa8e
-- title:
--   Canonical monic presentation of intermediate ideals in a time quotient
-- statement:
--   Let $A=\mathbb C[t,x_1,x_2,x_3]$. Choose $r_1,r_2,r_3\in\mathbb C[T]$ and let
--
--   $$\Phi:A\longrightarrow\mathbb C[T],\qquad
--   \Phi(t)=T,\quad\Phi(x_i)=r_i(T).$$
--
--   Write $E:\mathbb C[T]\to A$ for the lift $E(q)=q(t)$, so $\Phi E=\mathrm{id}$.
--   Let $M\in\mathbb C[T]$ be nonzero, and let $I\subseteq A$ satisfy
--
--   $$f\in I\quad\Longleftrightarrow\quad M\mid\Phi(f)\qquad(f\in A).$$
--
--   For every ideal $J\subseteq A$ containing $I$, there is a monic polynomial $g\in\mathbb C[T]$ such that
--
--   $$g\mid M,\qquad \deg g\le\deg M,$$
--
--   $$J=I+(E(g)),\qquad
--   f\in J\quad\Longleftrightarrow\quad g\mid\Phi(f)\qquad(f\in A).$$
--
--   The quotient $A/J$ is finite dimensional over $\mathbb C$, with
--
--   $$\dim_{\mathbb C}(A/J)=\deg g.$$
--
--   The polynomial $g$ is canonical: if a monic $h\in\mathbb C[T]$ also satisfies
--
--   $$f\in J\quad\Longleftrightarrow\quad h\mid\Phi(f)\qquad(f\in A),$$
--
--   then $h=g$. Thus every ideal above $I$ has a unique monic time-polynomial presentation, and its degree is its quotient length.
--
--   **Formalization Note** The hypotheses are the exact membership presentation, $M\ne0$, and $I\subseteq J$. No finite-dimensionality, finite-generation, contact, lattice or nonsingularity assumption is added. The displayed degrees are formal natural degrees; $M\ne0$ and monicity of $g$ make this harmless. The theorem allows $J=I$, $J=A$ and constant nonzero $M$. It asserts that one time polynomial generates $J$ modulo $I$, not that $J$ is principal in the four-variable ring. Uniqueness is among all monic polynomials satisfying the membership test; no separate divisor assumption on the competing $h$ is needed. No global zero estimate is asserted.
-- source:
--   Derived intermediate-ideal calculation for the finite-intersection algebra approach associated with Senthil Kumar K (2026), Appendix A, https://doi.org/10.1017/S001309152610145X. This exact classification statement is proved here, not quoted from the article. Map J to the univariate polynomial ring, choose its monic generator, and use the surjective ideal correspondence. Its generator divides M; a lifted remainder proves J=I+(g(t)). The first isomorphism theorem and the polynomial quotient power basis compute the length. Mutual divisibility proves uniqueness. Primary formal references: Polynomial.exists_monic_span, Ideal.map_comap_of_surjective, Ideal.comap_map_of_surjective', Ideal.quotientKerAlgEquivOfSurjective, AdjoinRoot.powerBasis and Polynomial.eq_of_monic_of_dvd_of_natDegree_le.

import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.AdjoinRoot

open scoped Classical

theorem WeierstrassEllipticZeta.triangular_intermediate_ideal_presentation
    (I : Ideal (MvPolynomial (Fin 4) ℂ)) (M : Polynomial ℂ)
    (r : Fin 3 → Polynomial ℂ) (hM : M ≠ 0)
    (hI : ∀ f : MvPolynomial (Fin 4) ℂ,
      f ∈ I ↔ M ∣ MvPolynomial.aeval (Fin.cons Polynomial.X r) f) :
    ∀ J : Ideal (MvPolynomial (Fin 4) ℂ), I ≤ J →
      ∃ g : Polynomial ℂ,
        g.Monic ∧ g ∣ M ∧ g.natDegree ≤ M.natDegree ∧
        J = I ⊔ Ideal.span {Polynomial.aeval (MvPolynomial.X (0 : Fin 4)) g} ∧
        (∀ f : MvPolynomial (Fin 4) ℂ,
          f ∈ J ↔ g ∣ MvPolynomial.aeval (Fin.cons Polynomial.X r) f) ∧
        FiniteDimensional ℂ (MvPolynomial (Fin 4) ℂ ⧸ J) ∧
        Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ J) = g.natDegree ∧
        (∀ h : Polynomial ℂ, h.Monic →
          (∀ f : MvPolynomial (Fin 4) ℂ,
            f ∈ J ↔ h ∣ MvPolynomial.aeval (Fin.cons Polynomial.X r) f) → h = g) := by sorry
