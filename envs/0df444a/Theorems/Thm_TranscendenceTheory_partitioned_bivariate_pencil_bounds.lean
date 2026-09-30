-- Prove2me | Theorems.Thm_TranscendenceTheory_partitioned_bivariate_pencil_bounds
-- name    : TranscendenceTheory.partitioned_bivariate_pencil_bounds
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-20T02:03:54.558958+00:00
-- url     : https://prove2.me/theorems/5e40679d-f6f3-4c3f-842e-46bfde06a5a1
-- title:
--   Separate zero and nonzero detector counts give tighter pencil bounds
-- statement:
--   Let R be an integral domain of characteristic zero, I a finite index type, and F a polynomial in R[T][Y]. Suppose each coefficient of F as a polynomial in Y has degree in T at most a. Fix families c_i,d_i in R, and put
--
--   $$I_0=\{i\in I:d_i=0\},\qquad I_1=\{i\in I:d_i\ne0\}.$$
--
--   The existence of nonnegative integers t,k in the ranges
--
--   $$t\le |I|a,\qquad k\le |I|,$$
--
--   such that
--
--   $$\prod_{i\in I}\bigl(F(t,c_i)+k d_i\bigr)\ne0$$
--
--   is equivalent to the existence of such integers in the tighter ranges
--
--   $$t\le |I_0|a,\qquad k\le |I_1|.$$
--
--   The formal witnesses use Fin of the corresponding upper bound plus one. The detector values d_i are fixed elements of R, independent of t. The same pair t,k is used at every index.
--
--   Empty index types, an empty part of the partition, a=0, repeated c_i, and zero individual values are included. The two counts add to |I|. In particular, if all d_i are nonzero then t=0 suffices, and if all d_i are zero then k=0 suffices whenever a certificate exists. Neither F nor the c_i,d_i are altered. No degree preservation under specialization is asserted.
-- source:
--   Derived refinement of bounded simultaneous specialization and bounded finite linear-combination nonvanishing, and equivalent reduction of https://prove2.me/theorems/d34f0ebd-9300-4a3a-8ed1-ebee75d0d32c. Reuses complete platform theorems bounded_bivariate_specialization (aa9fdd40-d30b-4f1e-aa4e-241e9f3bd925) and bounded_finite_pencil_nonvanishing (a4d2e3a6-7cf0-4761-9c5b-829b25bf7f3e). Primary Mathlib source at revision 0df444a360eaa60ab8c11dca51a86af692955474: Fintype.card_le_of_injective, line 240, https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Data/Fintype/Card.lean#L240. Mission context: Senthil Kumar K (2026), Algebraic independence of values of Weierstrass elliptic and zeta functions, Appendix A.2, Theorem A.3 and Proposition A.1, https://doi.org/10.1017/S001309152610145X. This refinement is derived here, not a verbatim theorem from the paper.

import Mathlib.Algebra.Polynomial.Bivariate
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Data.Fintype.Card

open scoped Classical

theorem TranscendenceTheory.partitioned_bivariate_pencil_bounds
    (R : Type*) [CommRing R] [IsDomain R] [CharZero R]
    (ι : Type*) [Fintype ι] (F : Polynomial (Polynomial R))
    (a : ℕ) (hdegree : ∀ j, (F.coeff j).natDegree ≤ a)
    (c d : ι → R) :
    (∃ t : Fin (Fintype.card ι * a + 1), ∃ k : Fin (Fintype.card ι + 1),
      (∏ i, ((F.map (Polynomial.evalRingHom (t.val : R))).eval (c i) +
        (k.val : R) * d i)) ≠ 0) ↔
    (∃ t : Fin (Fintype.card {i : ι // d i = 0} * a + 1),
      ∃ k : Fin (Fintype.card {i : ι // d i ≠ 0} + 1),
      (∏ i, ((F.map (Polynomial.evalRingHom (t.val : R))).eval (c i) +
        (k.val : R) * d i)) ≠ 0) := by sorry
