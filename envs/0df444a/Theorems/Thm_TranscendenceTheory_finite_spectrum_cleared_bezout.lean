-- Prove2me | Theorems.Thm_TranscendenceTheory_finite_spectrum_cleared_bezout
-- name    : TranscendenceTheory.finite_spectrum_cleared_bezout
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-20T00:32:33.622292+00:00
-- url     : https://prove2.me/theorems/38b38b87-13c5-4fe1-9f79-6d3df441f8d8
-- title:
--   Finite spectrum evaluation criterion for bounded polynomial Bezout certificates
-- statement:
--   Let R be an integral domain, let I be any finite index type, and let x_i in R be a family of spectrum points, with repetitions allowed. For f,h in R[Y], assume the natural degree e of f is positive and put
--
--   $$g(Y)=\prod_{i\in I}(Y-x_i).$$
--
--   The following are equivalent:
--
--   1. For every i, h(x_i)=0 implies f(x_i) is nonzero in R.
--   2. There are a nonzero d in R and u,v,w in R[Y] such that
--
--   $$uf+vg+wh=d,$$
--
--   with natural degrees of v and w strictly less than e, and the natural degree of u at most the maximum of those of g and h. The right-hand side is embedded as a constant polynomial in Y.
--
--   The convention is that the natural degree of the zero polynomial is zero. The theorem includes empty spectra, repeated points, and the zero detector h. It assumes neither that R is a field nor that its nonzero elements are units. No algebraic closedness, Noetherian, or unique-factorization hypothesis is needed. In particular, for R=C[T], nonzero means nonzero as a polynomial in T, not nonvanishing at every value of T.
--
--   This is a derived equivalence combining finite-product root detection with bounded root-avoidance certificates, descent from a field extension, and clearing denominators.
-- source:
--   Derived finite-spectrum evaluation equivalence and equivalent reduction of https://prove2.me/theorems/8fffdd60-8b36-4ddd-ae0f-ec5c40d3f51c. Primary source at Mathlib revision 0df444a360eaa60ab8c11dca51a86af692955474: Polynomial.eval_map_apply, line 580, and eval_prod, line 675, https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Algebra/Polynomial/Eval/Defs.lean#L580; Finset.prod_eq_zero and prod_eq_zero_iff, https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Algebra/BigOperators/GroupWithZero/Finset.lean#L30. Reuses complete platform theorems guarded_root_avoidance_bezout (9f4fe5da-b1a3-4c80-85ec-324ca0adc565), bounded_bezout_field_descent (a734d628-1bdd-46f4-9b4c-e61dc04d2020), and bounded_bezout_clear_denominators (1b650b1d-6a15-49d1-9504-3ea7e8bf2269). Mission context: Senthil Kumar K (2026), Algebraic independence of values of Weierstrass elliptic and zeta functions, Appendix A.2, Theorem A.3 and Proposition A.1, https://doi.org/10.1017/S001309152610145X. This equivalence is derived here, not a verbatim theorem from the paper.

import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Algebra.Polynomial.BigOperators

theorem TranscendenceTheory.finite_spectrum_cleared_bezout
    (R : Type*) [CommRing R] [IsDomain R]
    (ι : Type*) [Fintype ι] (x : ι → R)
    (f h : Polynomial R) (hf : f.natDegree ≠ 0) :
    (∀ i, h.eval (x i) = 0 → f.eval (x i) ≠ 0) ↔
      let g : Polynomial R := ∏ i, (Polynomial.X - Polynomial.C (x i))
      ∃ d : R, d ≠ 0 ∧ ∃ u v w : Polynomial R,
        u * f + v * g + w * h = Polynomial.C d ∧
        v.natDegree < f.natDegree ∧ w.natDegree < f.natDegree ∧
        u.natDegree ≤ max g.natDegree h.natDegree := by sorry
