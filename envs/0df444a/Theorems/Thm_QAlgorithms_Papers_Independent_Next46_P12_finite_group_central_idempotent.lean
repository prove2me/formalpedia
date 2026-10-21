-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P12_finite_group_central_idempotent
-- name    : QAlgorithms.Papers.Independent.Next46.P12.finite_group_central_idempotent
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T13:15:45.003697+00:00
-- url     : https://prove2.me/theorems/86c369ae-6322-4415-a187-57ab33b47357
-- title:
--   Corollary A.2 (Frobenius): character formula for group-algebra central idempotents
-- statement:
--   Let $G$ be a finite group and let $k$ be a characteristic-zero field such that $kG$ is split semisimple. For a simple left $kG$-module $V^\lambda$, let $\chi^\lambda$ be its trace character and let $\epsilon(\lambda)$ be the central projector acting as identity on this simple type and zero on all other simple types. Then
--
--   $$\epsilon(\lambda)=\frac{1}{|G|}\sum_{g\in G}\chi^\lambda(1)\chi^\lambda(g^{-1})\,g.$$
--
--   This is Frobenius’s character formula over a split characteristic-zero group algebra.
-- source:
--   Canonical idempotents of multiplicity-free families of algebras, arXiv:1606.08900v5, PDF p. 33, Corollary A.2 (Frobenius): character formula for group-algebra central idempotents

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P12

noncomputable section

open scoped BigOperators Classical

open Filter

namespace QAlgorithms.Papers.Independent.Next46.P12

universe u v w

variable {k : Type u} [Field k]

variable {A : Type v} [Ring A] [Algebra k A]

/-- Corollary A.2 (Frobenius), source PDF p. 33. Splitness is explicit; the
character is evaluated on g inverse over a general characteristic-zero field. -/
theorem finite_group_central_idempotent [CharZero k]
    {G : Type w} [Group G] [Fintype G]
    (D : SplitPresentation k (MonoidAlgebra k G)) (lam : D.Label) :
    centralIdempotent D lam = (Fintype.card G : k)⁻¹ •
      ∑ g : G, (simpleCharacter D lam 1 *
        simpleCharacter D lam (MonoidAlgebra.single g⁻¹ 1)) • MonoidAlgebra.single g 1 := by sorry

end QAlgorithms.Papers.Independent.Next46.P12

end
