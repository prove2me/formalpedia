-- Prove2me | Theorems.Thm_TranscendenceTheory_natural_root_bound_nonvanishing
-- name    : TranscendenceTheory.natural_root_bound_nonvanishing
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-20T03:48:47.235652+00:00
-- url     : https://prove2.me/theorems/b845f21d-a41e-41e8-906b-120a37338271
-- title:
--   Distinct natural roots bound a nonzero polynomial evaluation
-- statement:
--   Let R be an integral domain of characteristic zero, let p belong to R[T], and assume its natural degree is at most N. Form the finite set B by taking the distinct roots of p in R and pulling them back along the injective map from the nonnegative integers into R.
--
--   For a nonzero polynomial this means
--
--   $$B=\{n\in\mathbb N:p(n)=0\}.$$
--
--   For the zero polynomial use B empty, following Lean's convention that the stored multiset of roots of zero is empty. Then
--
--   $$|B|\le N,$$
--
--   and
--
--   $$\bigl(\exists\,n\in\mathbb N,\ n\le N,\ p(n)\ne0\bigr)
--   \quad\Longleftrightarrow\quad
--   \bigl(\exists\,n\in\mathbb N,\ n\le |B|,\ p(n)\ne0\bigr).$$
--
--   Only distinct roots that are nonnegative integer values count toward the new bound. Other roots and root multiplicities contribute nothing. If p is zero, both existence statements are false; the empty-root convention does not supply a nonvanishing witness. Nonzero constant polynomials have B empty and admit the witness zero.
-- source:
--   Derived natural-number root-count refinement of bounded polynomial nonvanishing, and equivalent reduction of https://prove2.me/theorems/0d340837-597c-43dc-9b2d-47f625bc1fb3. Primary Mathlib source at revision 0df444a360eaa60ab8c11dca51a86af692955474: Polynomial.card_roots', https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Algebra/Polynomial/Roots.lean#L80, Finset.exists_mem_notMem_of_card_lt_card in Data/Finset/Card.lean, line 614, and Finset.card_preimage in Data/Finset/Preimage.lean, line 103. Mission context: Senthil Kumar K (2026), Algebraic independence of values of Weierstrass elliptic and zeta functions, Appendix A.2, Theorem A.3 and Proposition A.1, https://doi.org/10.1017/S001309152610145X. This refinement is derived here, not a verbatim theorem from the paper.

import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Finset.Preimage

open scoped Classical

theorem TranscendenceTheory.natural_root_bound_nonvanishing
    (R : Type*) [CommRing R] [IsDomain R] [CharZero R]
    (p : Polynomial R) (N : ℕ) (hdegree : p.natDegree ≤ N) :
    let B : Finset ℕ := p.roots.toFinset.preimage (Nat.cast : ℕ → R)
      Nat.cast_injective.injOn
    B.card ≤ N ∧
    ((∃ n : Fin (N + 1), p.eval (n.val : R) ≠ 0) ↔
      ∃ n : Fin (B.card + 1), p.eval (n.val : R) ≠ 0) := by sorry
