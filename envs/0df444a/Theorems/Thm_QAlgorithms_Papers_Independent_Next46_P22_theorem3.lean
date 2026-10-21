-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P22_theorem3
-- name    : QAlgorithms.Papers.Independent.Next46.P22.theorem3
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T13:46:03.336696+00:00
-- url     : https://prove2.me/theorems/e61e25d1-74ef-4637-b72a-2650f0c0b43f
-- title:
--   Theorem 3
-- statement:
--   Let $F$ have characteristic zero, $H$ be a finite-dimensional semisimple Hopf algebra over $F$, and $L$ a finite-dimensional left $H$-module Lie algebra. For its actual solvable radical $R$, there exists a maximal semisimple subalgebra $B$ such that both $B,R$ are invariant and
--
--   $$L=B\oplus R$$
--
--   as an internal sum of $H$-submodules. No invariant radical or Levi factor is given as input, and no algebraic closure is assumed.
-- source:
--   Structure of H-(co)module Lie algebras, arXiv:1205.0778v7, PDF p. 10, Theorem 3

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P22

namespace QAlgorithms.Papers.Independent.Next46.P22

noncomputable section

open scoped TensorProduct

open Classical

section Statements

variable {F H L : Type*} [Field F] [Ring H] [HopfAlgebra F H] [LieRing L] [LieAlgebra F L]

variable {V W : Type*} [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]

/-- Theorem 3, PDF p.10: both chosen B and actual R are invariant. -/
theorem theorem3 [CharZero F] [FiniteDimensional F H] [IsSemisimpleRing H]
    [FiniteDimensional F L] (alpha : H →ₐ[F] Module.End F L) (ha : ModuleLie alpha) :
    ∃ B : LieSubalgebra F L, MaximalSemisimple B ∧ ActionStable alpha B.toSubmodule ∧
      ActionStable alpha (LieAlgebra.radical F L).toSubmodule ∧
      IsCompl B.toSubmodule (LieAlgebra.radical F L).toSubmodule := by sorry

end Statements

end

end QAlgorithms.Papers.Independent.Next46.P22
