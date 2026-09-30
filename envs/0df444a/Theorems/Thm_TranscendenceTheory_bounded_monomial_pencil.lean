-- Prove2me | Theorems.Thm_TranscendenceTheory_bounded_monomial_pencil
-- name    : TranscendenceTheory.bounded_monomial_pencil
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-20T03:02:05.90758+00:00
-- url     : https://prove2.me/theorems/998c6947-763d-480b-a240-162d9f38de92
-- title:
--   A single bounded integer suffices along a monomial pencil
-- statement:
--   Let R be an integral domain of characteristic zero and I a finite index set. Let F belong to R[T][Y], with every coefficient in Y having T-degree at most a, and fix families c,d from I to R. Set
--
--   $$z=|\{i\in I:d_i=0\}|,\qquad q=|\{i\in I:d_i\ne0\}|.$$
--
--   The following two certificates are equivalent:
--
--   $$\exists\,t,k\in\mathbb N,\quad t\le az,\quad k\le q,\quad
--   \prod_{i\in I}\bigl(F(t,c_i)+k d_i\bigr)\ne0;$$
--
--   $$\exists\,r\in\mathbb N,\quad r\le az+(a+1)q,\quad
--   \prod_{i\in I}\bigl(F(r,c_i)+r^{a+1}d_i\bigr)\ne0.$$
--
--   Thus a bounded search over two independently chosen integers can be replaced by a bounded search along the fixed monomial path with second coordinate equal to the first raised to the power a+1. The degree bound prevents cancellation of the added term on every index with nonzero detector. Empty families, empty parts of the partition, repeated values and a=0 are included.
--
--   The converse may select a new pair of integers: the monomial coefficient itself need not satisfy the original bound q. The theorem preserves existence of certificates; it does not assert that the new search is smaller in every parameter regime.
-- source:
--   Derived bounded monomial-pencil equivalence and equivalent reduction of https://prove2.me/theorems/f35a3dcf-a6e0-434d-9853-095df344010e. Primary Mathlib source at revision 0df444a360eaa60ab8c11dca51a86af692955474: Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero, https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Algebra/Polynomial/Roots.lean#L722, and Polynomial.coeff_eq_zero_of_natDegree_lt in Algebra/Polynomial/Degree/Operations.lean, line 85. Reuses complete platform theorems bounded_bivariate_specialization (aa9fdd40-d30b-4f1e-aa4e-241e9f3bd925) and bounded_finite_pencil_nonvanishing (a4d2e3a6-7cf0-4761-9c5b-829b25bf7f3e). Mission context: Senthil Kumar K (2026), Algebraic independence of values of Weierstrass elliptic and zeta functions, Appendix A.2, Theorem A.3 and Proposition A.1, https://doi.org/10.1017/S001309152610145X. The monomial-path equivalence is derived here, not a verbatim theorem from the paper.

import Mathlib.Algebra.Polynomial.Bivariate
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Data.Fintype.Card

open scoped Classical

theorem TranscendenceTheory.bounded_monomial_pencil
    (R : Type*) [CommRing R] [IsDomain R] [CharZero R]
    (ι : Type*) [Fintype ι] (F : Polynomial (Polynomial R))
    (a : ℕ) (hdegree : ∀ j, (F.coeff j).natDegree ≤ a)
    (c d : ι → R) :
    (∃ t : Fin (Fintype.card {i : ι // d i = 0} * a + 1),
      ∃ k : Fin (Fintype.card {i : ι // d i ≠ 0} + 1),
      (∏ i, ((F.map (Polynomial.evalRingHom (t.val : R))).eval (c i) +
        (k.val : R) * d i)) ≠ 0) ↔
    (∃ r : Fin (Fintype.card {i : ι // d i = 0} * a +
        Fintype.card {i : ι // d i ≠ 0} * (a + 1) + 1),
      (∏ i, ((F.map (Polynomial.evalRingHom (r.val : R))).eval (c i) +
        (r.val : R) ^ (a + 1) * d i)) ≠ 0) := by sorry
