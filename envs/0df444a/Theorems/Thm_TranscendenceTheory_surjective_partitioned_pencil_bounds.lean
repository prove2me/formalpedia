-- Prove2me | Theorems.Thm_TranscendenceTheory_surjective_partitioned_pencil_bounds
-- name    : TranscendenceTheory.surjective_partitioned_pencil_bounds
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-20T02:26:32.780181+00:00
-- url     : https://prove2.me/theorems/7b9e6f47-2ae3-4d16-9882-bee799f4a747
-- title:
--   Surjective reindexing preserves bounded pencil certificates
-- statement:
--   Let R be an integral domain of characteristic zero, let I and J be finite sets, and let
--
--   $$\pi:I\longrightarrow J$$
--
--   be surjective. Let F belong to R[T][Y], assume every coefficient of F as a polynomial in Y has T-degree at most a, and fix families c and d from J to R. For K=J use the given families; for K=I pull them back along pi. Write
--
--   $$z_K=|\{x\in K:d_x=0\}|,\qquad q_K=|\{x\in K:d_x\ne0\}|.$$
--
--   Define the bounded certificate
--
--   $$\mathcal C(K)\quad\Longleftrightarrow\quad
--   \exists\,t,k\in\mathbb N,\quad
--   t\le az_K,\quad k\le q_K,\quad
--   \prod_{x\in K}\bigl(F(t,c_x)+k d_x\bigr)\ne0.$$
--
--   Then
--
--   $$\mathcal C(I)\quad\Longleftrightarrow\quad\mathcal C(J).$$
--
--   Thus a surjective reindexing can remove repeated entries from a nonvanishing certificate while reducing both integer bounds to the corresponding counts in the smaller index set. The integers may be reselected in the forward direction. The theorem does not equate the numerical values of the two products. Empty sets, empty parts of the zero/nonzero partition, repeated values, and a=0 are included.
-- source:
--   Derived surjective-reindexing theorem for bounded polynomial pencil certificates, and equivalent reduction of https://prove2.me/theorems/e515f1b6-6149-4f08-bd4c-64b27d108fd8. Reuses complete platform theorems bounded_bivariate_specialization (aa9fdd40-d30b-4f1e-aa4e-241e9f3bd925) and bounded_finite_pencil_nonvanishing (a4d2e3a6-7cf0-4761-9c5b-829b25bf7f3e). Primary Mathlib source at revision 0df444a360eaa60ab8c11dca51a86af692955474: Fintype.card_le_of_surjective in https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Data/Fintype/Card.lean. Mission context: Senthil Kumar K (2026), Algebraic independence of values of Weierstrass elliptic and zeta functions, Appendix A.2, Theorem A.3 and Proposition A.1, https://doi.org/10.1017/S001309152610145X. This refinement is derived here, not a verbatim theorem from the paper.

import Mathlib.Algebra.Polynomial.Bivariate
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Data.Fintype.Card

open scoped Classical

theorem TranscendenceTheory.surjective_partitioned_pencil_bounds
    (R : Type*) [CommRing R] [IsDomain R] [CharZero R]
    (ι κ : Type*) [Fintype ι] [Fintype κ]
    (π : ι → κ) (hπ : Function.Surjective π)
    (F : Polynomial (Polynomial R)) (a : ℕ)
    (hdegree : ∀ j, (F.coeff j).natDegree ≤ a) (c d : κ → R) :
    (∃ t : Fin (Fintype.card {i : ι // d (π i) = 0} * a + 1),
      ∃ k : Fin (Fintype.card {i : ι // d (π i) ≠ 0} + 1),
      (∏ i, ((F.map (Polynomial.evalRingHom (t.val : R))).eval (c (π i)) +
        (k.val : R) * d (π i))) ≠ 0) ↔
    (∃ t : Fin (Fintype.card {j : κ // d j = 0} * a + 1),
      ∃ k : Fin (Fintype.card {j : κ // d j ≠ 0} + 1),
      (∏ j, ((F.map (Polynomial.evalRingHom (t.val : R))).eval (c j) +
        (k.val : R) * d j)) ≠ 0) := by sorry
