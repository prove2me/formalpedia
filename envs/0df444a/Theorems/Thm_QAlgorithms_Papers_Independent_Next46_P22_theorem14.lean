-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P22_theorem14
-- name    : QAlgorithms.Papers.Independent.Next46.P22.theorem14
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T13:53:08.97564+00:00
-- url     : https://prove2.me/theorems/e59f300d-4eb6-42a4-8313-78e009520046
-- title:
--   Theorem 14
-- statement:
--   Let $F$ have characteristic zero, $G$ be finite and $L$ a finite-dimensional $G$-graded Lie algebra over $F$. Write $R=\operatorname{rad}(L)$ and $N=\operatorname{nilrad}(L)$. There exist a graded maximal semisimple subalgebra $B$ and graded subspace $S$, with $R,N$ also graded, such that
--
--   $$R=S\oplus N,\qquad L=B\oplus S\oplus N,\qquad [B,S]=0.$$
--
--   The sums are internal sums of graded subspaces. The group need not be abelian, but its finiteness is retained. Neither $S$ being abelian nor $S$ being an ideal is asserted.
-- source:
--   Structure of H-(co)module Lie algebras, arXiv:1205.0778v7, PDF p. 14, Theorem 14

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P22

namespace QAlgorithms.Papers.Independent.Next46.P22

noncomputable section

open scoped TensorProduct

open Classical

section Statements

variable {F H L : Type*} [Field F] [Ring H] [HopfAlgebra F H] [LieRing L] [LieAlgebra F L]

variable {V W : Type*} [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]

/-- Theorem 14, PDF p.14: finite G; B,S and both actual radicals are graded. -/
theorem theorem14 [CharZero F] [FiniteDimensional F L]
    {G : Type*} [Group G] [Finite G] (D : Grading F G L) (hD : GradedLie D) :
    ∃ B : LieSubalgebra F L, ∃ S : Submodule F L,
      RadicalDecomposition (GradedSubspace D) B S := by sorry

end Statements

end

end QAlgorithms.Papers.Independent.Next46.P22
