-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_finite_colength_bounded_time_escape
-- name    : WeierstrassEllipticZeta.finite_colength_bounded_time_escape
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-09T16:01:59.99195+00:00
-- url     : https://prove2.me/theorems/d9368ac8-24e4-46c1-991a-198aa8a1e394
-- title:
--   Bounded time-polynomial escape from a proper finite-colength ideal
-- statement:
--   Let $A$ be a commutative complex algebra, let $D:A\to A$ be a
--   complex-linear derivation, and let $t\in A$ satisfy $D(t)=1$.
--   Let $I\subsetneq A$ be an ideal for which $A/I$ is finite dimensional
--   over $\mathbb C$.
--
--   There exists a monic polynomial $g\in\mathbb C[T]$ such that
--
--   $$0<\deg g\leq\dim_{\mathbb C}(A/I),$$
--
--   and, for every $q\in\mathbb C[T]$,
--
--   $$q(t)\in I\quad\Longleftrightarrow\quad g\mid q.$$
--
--   Moreover,
--
--   $$g(t)\in I,\qquad D(g(t))=g'(t)\notin I,
--   \qquad \deg g'<\deg g.$$
--
--   Thus an element escaping the ideal under differentiation can be chosen
--   as a polynomial in the time coordinate with degree bounded by the
--   quotient dimension. The hypotheses concern only the dimension of the
--   quotient; $A$ itself need not be finite dimensional. The polynomial $g$
--   can be chosen as the minimal polynomial of the class of $t$ in $A/I$.
-- source:
--   Derived differential-algebra step for the differential polynomial-ring method associated with Senthil Kumar K (2026), Appendix A introductory paragraphs and Theorem A.2, https://doi.org/10.1017/S001309152610145X. This exact bounded escape statement is derived here, not quoted from the article. The minimal polynomial of the time class in the finite quotient generates all univariate time-polynomial relations and has positive degree at most the quotient dimension. Its derivative is nonzero of smaller degree, so cannot also be a relation. The identity D(t)=1 identifies evaluation of this derivative with the derivative of the chosen element. Primary formal references: minpoly.monic, minpoly.natDegree_pos, minpoly.natDegree_le, minpoly.dvd_iff, Derivation.map_aeval, Polynomial.derivative_ne_zero, Polynomial.natDegree_derivative_lt and Polynomial.natDegree_le_of_dvd.

import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

open scoped Classical

theorem WeierstrassEllipticZeta.finite_colength_bounded_time_escape
    (A : Type*) [CommRing A] [Algebra ℂ A]
    (D : Derivation ℂ A A) (t : A) (ht : D t = 1)
    (I : Ideal A) [FiniteDimensional ℂ (A ⧸ I)] (hI : I ≠ ⊤) :
    ∃ g : Polynomial ℂ,
      g.Monic ∧ 0 < g.natDegree ∧
      g.natDegree ≤ Module.finrank ℂ (A ⧸ I) ∧
      (∀ q : Polynomial ℂ, Polynomial.aeval t q ∈ I ↔ g ∣ q) ∧
      Polynomial.aeval t g ∈ I ∧
      D (Polynomial.aeval t g) = Polynomial.aeval t g.derivative ∧
      g.derivative.natDegree < g.natDegree ∧
      D (Polynomial.aeval t g) ∉ I := by sorry
