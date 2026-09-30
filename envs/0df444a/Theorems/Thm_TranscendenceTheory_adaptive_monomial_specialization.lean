-- Prove2me | Theorems.Thm_TranscendenceTheory_adaptive_monomial_specialization
-- name    : TranscendenceTheory.adaptive_monomial_specialization
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-20T03:25:00.082342+00:00
-- url     : https://prove2.me/theorems/bc4f7044-863b-42f5-9d9d-b343422b15c7
-- title:
--   Actual polynomial degrees sharpen monomial specialization bounds
-- statement:
--   Let R be an integral domain of characteristic zero, I a finite set, and let each polynomial f_i in R[T] have natural degree at most a. Fix values d_i in R and set
--
--   $$I_0=\{i:d_i=0\},\quad I_1=\{i:d_i\ne0\},\quad z=|I_0|,\quad q=|I_1|.$$
--
--   Use the actual degrees to define
--
--   $$\delta=\max\bigl(\{\deg f_i:i\in I_1\}\cup\{0\}\bigr),\qquad
--   E=\sum_{i\in I_0}\deg f_i,$$
--
--   where the degree notation here means natural degree, with the zero polynomial assigned degree zero. Define the two bounds
--
--   $$D=az+(a+1)q,\qquad D'=E+(\delta+1)q.$$
--
--   Then
--
--   $$\delta\le a,\qquad D'\le D,$$
--
--   and the following certificates are equivalent:
--
--   $$\exists\,r\in\mathbb N,\quad r\le D,\quad
--   \prod_i\bigl(f_i(r)+r^{a+1}d_i\bigr)\ne0;$$
--
--   $$\exists\,s\in\mathbb N,\quad s\le D',\quad
--   \prod_i\bigl(f_i(s)+s^{\delta+1}d_i\bigr)\ne0.$$
--
--   Thus both the exponent and the search limit can use the actual degrees without increasing either bound. The integer may be reselected because the exponent changes. The maximum over an empty nonzero-detector part is zero. Empty families and partition parts, repeated polynomials, zero polynomials and a=0 are all included; a zero polynomial on I_0 makes both certificates impossible.
-- source:
--   Derived actual-degree refinement of bounded monomial nonvanishing, and equivalent reduction of https://prove2.me/theorems/03baf9f2-ea7a-4f0d-a6b8-2ee538fecdc1. Refines the uniform bound in https://prove2.me/theorems/998c6947-763d-480b-a240-162d9f38de92. Primary Mathlib source at revision 0df444a360eaa60ab8c11dca51a86af692955474: Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero, https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Algebra/Polynomial/Roots.lean#L722, and Polynomial.natDegree_prod_le in Algebra/Polynomial/BigOperators.lean, line 137. Mission context: Senthil Kumar K (2026), Algebraic independence of values of Weierstrass elliptic and zeta functions, Appendix A.2, Theorem A.3 and Proposition A.1, https://doi.org/10.1017/S001309152610145X. The actual-degree refinement is derived here, not a verbatim theorem from the paper.

import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Eval.Degree

open scoped Classical

theorem TranscendenceTheory.adaptive_monomial_specialization
    (R : Type*) [CommRing R] [IsDomain R] [CharZero R]
    (ι : Type*) [Fintype ι] (f : ι → Polynomial R) (d : ι → R)
    (a : ℕ) (hdegree : ∀ i, (f i).natDegree ≤ a) :
    let b : ℕ := Finset.univ.sup (fun i : {i : ι // d i ≠ 0} => (f i.val).natDegree)
    b ≤ a ∧
    ((∑ i : {i : ι // d i = 0}, (f i.val).natDegree) +
      Fintype.card {i : ι // d i ≠ 0} * (b + 1) ≤
      Fintype.card {i : ι // d i = 0} * a + Fintype.card {i : ι // d i ≠ 0} * (a + 1)) ∧
    ((∃ r : Fin (Fintype.card {i : ι // d i = 0} * a +
        Fintype.card {i : ι // d i ≠ 0} * (a + 1) + 1),
      (∏ i, ((f i).eval (r.val : R) + (r.val : R) ^ (a + 1) * d i)) ≠ 0) ↔
    (∃ r : Fin ((∑ i : {i : ι // d i = 0}, (f i.val).natDegree) +
        Fintype.card {i : ι // d i ≠ 0} * (b + 1) + 1),
      (∏ i, ((f i).eval (r.val : R) + (r.val : R) ^ (b + 1) * d i)) ≠ 0)) := by sorry
