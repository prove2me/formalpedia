-- Prove2me | Theorems.Thm_WeilConjectures_exists_unit_equiv_of_snf_diag_eq
-- name    : WeilConjectures.exists_unit_equiv_of_snf_diag_eq
-- status  : Open
-- author  : @pageman
-- created : 2026-11-24T05:24:19.25783+00:00
-- url     : https://prove2.me/theorems/4cb5f2d7-b29d-4478-9e1c-d8a5933517ed
-- title:
--   Unit Equivalence from Equal SNF Diagonals
-- statement:
--   Let $K$ be a field, $\iota$ a finite index type, and $d$ a diagonal assignment admitting, for every $M \in M_\iota(K[X])$, a factorization $P M Q = \operatorname{diag}(d(M))$ with unit-determinant $P,Q$. If $d(M)=d(N)$, then $M$ and $N$ are equivalent over $K[X]$: there exist unit-determinant $P',Q'$ with
--   $$P'\, M\, Q' = N.$$
--
--   Compose the two Smith factorizations through the common diagonal (A41a).
-- source:
--   Matrix.isUnit_iff_isUnit_det; Matrix.nonsing_inv; Hoffman–Kunze, Linear Algebra, Ch. 6

import Mathlib

/-- A41a: if `d` admits unit Smith factorizations and `d M = d N`, then `M` and `N`
are equivalent over `K[X]`: ∃ unit-det `P,Q` with `P * M * Q = N`.

**REUSE:** `Matrix.isUnit_iff_isUnit_det`, `Matrix.nonsing_inv`. -/

theorem WeilConjectures.exists_unit_equiv_of_snf_diag_eq
    {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]
    (d : Matrix ι ι (Polynomial K) → (ι → Polynomial K))
    (hfac : ∀ M, ∃ (P Q : Matrix ι ι (Polynomial K)),
      IsUnit P.det ∧ IsUnit Q.det ∧
        P * M * Q = Matrix.diagonal (d M))
    {M N : Matrix ι ι (Polynomial K)}
    (h : d M = d N) :
    ∃ (P Q : Matrix ι ι (Polynomial K)),
      IsUnit P.det ∧ IsUnit Q.det ∧ P * M * Q = N := by
  sorry
