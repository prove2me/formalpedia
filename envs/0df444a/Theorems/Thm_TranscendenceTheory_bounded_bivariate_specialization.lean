-- Prove2me | Theorems.Thm_TranscendenceTheory_bounded_bivariate_specialization
-- name    : TranscendenceTheory.bounded_bivariate_specialization
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-20T00:52:22.007986+00:00
-- url     : https://prove2.me/theorems/aa9fdd40-d30b-4f1e-aa4e-241e9f3bd925
-- title:
--   Simultaneous bivariate specialization at a bounded integer
-- statement:
--   Let R be an integral domain of characteristic zero, let I be a finite index type, and let F be a polynomial in R[T][Y]. Let a be a natural number such that every coefficient of F, viewed as a polynomial in Y, has degree in T at most a. Let c_i be any family of elements of R, and let P(i) be any predicate specifying which indices are active.
--
--   The following are equivalent:
--
--   1. For every active i, the polynomial F(T,c_i) is nonzero in R[T].
--   2. There exists a nonnegative integer n with
--
--   $$0\le n\le |I|a$$
--
--   such that, for every active i,
--
--   $$F(n,c_i)\ne0\quad\text{in }R.$$
--
--   The same n works for all active indices. In the formal statement, n is an element of Fin(|I|a+1), and F(n,Y) is obtained by mapping each coefficient of F through evaluation at the image of n in R.
--
--   Repeated c_i, empty index types, an empty active set, and a=0 are included. There is no positivity assumption on the degree of F in Y. No field or algebraic-closedness hypothesis is required. Characteristic zero ensures that the integer sampling points are distinct.
--
--   This is a quantitative simultaneous-specialization equivalence derived from the polynomial root bound. It asserts no preservation of the degree in Y after specialization.
-- source:
--   Derived bounded simultaneous specialization equivalence and equivalent reduction of https://prove2.me/theorems/ca8e597a-f476-4290-baed-4486534506f5. Primary sources at Mathlib revision 0df444a360eaa60ab8c11dca51a86af692955474: Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero, line 722, https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Algebra/Polynomial/Roots.lean#L722; Polynomial.map_evalRingHom_eval, line 162, https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Algebra/Polynomial/Bivariate.lean#L162; Polynomial.natDegree_sum_le_of_forall_le and natDegree_prod_le, https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Algebra/Polynomial/BigOperators.lean#L65. Mission context: Senthil Kumar K (2026), Algebraic independence of values of Weierstrass elliptic and zeta functions, Appendix A.2, Theorem A.3 and Proposition A.1, https://doi.org/10.1017/S001309152610145X. The equivalence is derived here and is not a verbatim theorem from the paper.

import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Bivariate
import Mathlib.Algebra.Polynomial.Eval.Degree

theorem TranscendenceTheory.bounded_bivariate_specialization
    (R : Type*) [CommRing R] [IsDomain R] [CharZero R]
    (ι : Type*) [Fintype ι] (F : Polynomial (Polynomial R))
    (a : ℕ) (hdegree : ∀ j, (F.coeff j).natDegree ≤ a)
    (c : ι → R) (active : ι → Prop) :
    (∀ i, active i → F.eval (Polynomial.C (c i)) ≠ 0) ↔
      ∃ n : Fin (Fintype.card ι * a + 1), ∀ i, active i →
        (F.map (Polynomial.evalRingHom (n.val : R))).eval (c i) ≠ 0 := by sorry
