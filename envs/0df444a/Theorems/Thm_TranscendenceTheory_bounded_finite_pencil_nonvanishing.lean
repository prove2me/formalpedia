-- Prove2me | Theorems.Thm_TranscendenceTheory_bounded_finite_pencil_nonvanishing
-- name    : TranscendenceTheory.bounded_finite_pencil_nonvanishing
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-20T01:05:52.635482+00:00
-- url     : https://prove2.me/theorems/a4d2e3a6-7cf0-4761-9c5b-829b25bf7f3e
-- title:
--   A bounded integer linear combination avoiding finitely many zeros
-- statement:
--   Let R be an integral domain of characteristic zero, let I be a finite index type, and let u_i,v_i be two families of elements of R. The following are equivalent:
--
--   1. For every i, if v_i=0 then u_i is nonzero; equivalently, no pair (u_i,v_i) is (0,0).
--   2. There is a nonnegative integer k with 0<=k<=|I| such that
--
--   $$\prod_{i\in I}(u_i+k v_i)\ne0\quad\text{in }R.$$
--
--   Here integers are mapped into R by its natural-number map. The formal witness has type Fin(|I|+1). The same k works at every index.
--
--   The theorem includes the empty index type, repeated pairs, and zero entries in either family. No field, division, or algebraic-closedness assumption is needed. Characteristic zero makes the integer test values distinct, and the integral-domain hypothesis makes products of nonzero polynomials nonzero.
--
--   This gives an explicitly bounded member of a family of linear combinations whose values are simultaneously nonzero. It is derived from the polynomial root bound.
-- source:
--   Derived bounded linear-combination avoidance theorem and equivalent reduction of https://prove2.me/theorems/f3495117-9241-4aad-a669-bb476a0bdbaf. Primary Mathlib source at revision 0df444a360eaa60ab8c11dca51a86af692955474: Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero, line 722, https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Algebra/Polynomial/Roots.lean#L722; Polynomial.natDegree_prod_le, line 137, https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Algebra/Polynomial/BigOperators.lean#L137. Mission context: Senthil Kumar K (2026), Algebraic independence of values of Weierstrass elliptic and zeta functions, Appendix A.2, Theorem A.3 and Proposition A.1, https://doi.org/10.1017/S001309152610145X. This equivalence is derived here, not a verbatim theorem from the paper.

import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Eval.Degree

theorem TranscendenceTheory.bounded_finite_pencil_nonvanishing
    (R : Type*) [CommRing R] [IsDomain R] [CharZero R]
    (ι : Type*) [Fintype ι] (u v : ι → R) :
    (∀ i, v i = 0 → u i ≠ 0) ↔
      ∃ n : Fin (Fintype.card ι + 1), (∏ i, (u i + (n.val : R) * v i)) ≠ 0 := by sorry
