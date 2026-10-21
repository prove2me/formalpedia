-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P22_theorem13
-- name    : QAlgorithms.Papers.Independent.Next46.P22.theorem13
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T13:34:43.299711+00:00
-- url     : https://prove2.me/theorems/67675ffd-2195-479a-8007-de98d6a14180
-- title:
--   Theorem 13 (abstract structural capstone; original seed)
-- statement:
--   Let $F$ be a field of characteristic zero, $H$ a finite-dimensional semisimple Hopf algebra over $F$, and $L$ a finite-dimensional $F$-Lie algebra. Suppose $L$ is a left $H$-module Lie algebra, or separately a right $H$-comodule Lie algebra. Write $R=\operatorname{rad}(L)$ and $N=\operatorname{nilrad}(L)$ for its actual solvable and nilpotent radicals. There exist a maximal semisimple subalgebra $B$ and a subspace $S$ such that all summands are invariant for the supplied action or coaction, and
--
--   $$R=S\oplus N,\qquad L=B\oplus S\oplus N,\qquad [B,S]=0.$$
--
--   These are internal vector-space direct sums. The statement supplies both the module and comodule versions and does not assert that $S$ is an ideal or abelian. It refines Levi decomposition by separating the nilpotent radical.
-- source:
--   Structure of H-(co)module Lie algebras, arXiv:1205.0778v7, PDF p. 14, Theorem 13 (abstract structural capstone; original seed)

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P22

namespace QAlgorithms.Papers.Independent.Next46.P22

noncomputable section

open scoped TensorProduct

open Classical

section Statements

variable {F H L : Type*} [Field F] [Ring H] [HopfAlgebra F H] [LieRing L] [LieAlgebra F L]

/-- Theorem 13, PDF p.14 (abstract p.1): BOTH module and comodule versions;
both B and S are produced, with the actual radicals and all summands invariant. -/
theorem theorem13 [CharZero F] [FiniteDimensional F H] [IsSemisimpleRing H]
    [FiniteDimensional F L] :
    (∀ alpha : H →ₐ[F] Module.End F L, ModuleLie alpha →
      ∃ B : LieSubalgebra F L, ∃ S : Submodule F L,
        RadicalDecomposition (ActionStable alpha) B S) ∧
    (∀ rho : RightComodule F H L, ComoduleLie rho →
      ∃ B : LieSubalgebra F L, ∃ S : Submodule F L,
        RadicalDecomposition (CoStable rho) B S) := by sorry

end Statements

end

end QAlgorithms.Papers.Independent.Next46.P22
