-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P22_theorem2
-- name    : QAlgorithms.Papers.Independent.Next46.P22.theorem2
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T13:44:22.235194+00:00
-- url     : https://prove2.me/theorems/874c0470-99de-482a-97aa-18861cc2d8e8
-- title:
--   Theorem 2
-- statement:
--   Let $F$ have characteristic zero, $H$ be any Hopf algebra over $F$, and $L$ a finite-dimensional right $H$-comodule Lie algebra. Assume its actual solvable radical $R$ is a subcomodule and $H$ admits a left integral $t$ that is ad-invariant and satisfies $t(1)=1$. There exists a maximal semisimple subalgebra $B$ that is a subcomodule, with
--
--   $$L=B\oplus R.$$
--
--   The sum is internal as $F$-vector spaces and as comodules. This is invariant Levi existence over the original field; it does not include a conjugacy theorem.
-- source:
--   Structure of H-(co)module Lie algebras, arXiv:1205.0778v7, PDF p. 9, Theorem 2

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P22

namespace QAlgorithms.Papers.Independent.Next46.P22

noncomputable section

open scoped TensorProduct

open Classical

section Statements

variable {F H L : Type*} [Field F] [Ring H] [HopfAlgebra F H] [LieRing L] [LieAlgebra F L]

variable {V W : Type*} [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]

/-- Theorem 2, PDF pp.9–10: invariant Levi existence, with radical stability
assumed for general H. Neither algebraic closure nor conjugacy is asserted. -/
theorem theorem2 [CharZero F] [FiniteDimensional F L]
    (rho : RightComodule F H L) (hr : ComoduleLie rho)
    (hR : CoStable rho (LieAlgebra.radical F L).toSubmodule)
    (t : H →ₗ[F] F) (ht : NormalizedAdIntegral t) :
    ∃ B : LieSubalgebra F L, MaximalSemisimple B ∧ CoStable rho B.toSubmodule ∧
      IsCompl B.toSubmodule (LieAlgebra.radical F L).toSubmodule := by sorry

end Statements

end

end QAlgorithms.Papers.Independent.Next46.P22
