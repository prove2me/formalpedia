-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P22_theorem1
-- name    : QAlgorithms.Papers.Independent.Next46.P22.theorem1
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T13:40:50.099679+00:00
-- url     : https://prove2.me/theorems/a776ea3f-2c17-4e57-bb32-a504ecbced39
-- title:
--   Theorem 1
-- statement:
--   Let $F$ be a field of characteristic zero, $H$ a finite-dimensional semisimple Hopf algebra over $F$, and $L$ a finite-dimensional left $H$-module Lie algebra. Its actual solvable radical $R=\operatorname{rad}(L)$ and nilpotent radical $N=\operatorname{nilrad}(L)$ are $H$-invariant:
--
--   $$R,N\ \text{are stable for the supplied Hopf structure}.$$
--
--   Both stability assertions are conclusions. Finite semisimplicity may equivalently be read as cosemisimplicity here. No algebraic closure of $F$ is assumed.
-- source:
--   Structure of H-(co)module Lie algebras, arXiv:1205.0778v7, PDF p. 6, Theorem 1

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P22

namespace QAlgorithms.Papers.Independent.Next46.P22

noncomputable section

open scoped TensorProduct

open Classical

section Statements

variable {F H L : Type*} [Field F] [Ring H] [HopfAlgebra F H] [LieRing L] [LieAlgebra F L]

/-- Theorem 1, PDF p.6: both invariance assertions are conclusions. -/
theorem theorem1 [CharZero F] [FiniteDimensional F H] [IsSemisimpleRing H]
    [FiniteDimensional F L] (alpha : H →ₐ[F] Module.End F L) (ha : ModuleLie alpha) :
    ActionStable alpha (LieAlgebra.radical F L).toSubmodule ∧
    ActionStable alpha (lieNilpotentRadical F L).toSubmodule := by sorry

end Statements

end

end QAlgorithms.Papers.Independent.Next46.P22
