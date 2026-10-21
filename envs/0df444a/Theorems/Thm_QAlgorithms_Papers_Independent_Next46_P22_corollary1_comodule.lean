-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P22_corollary1_comodule
-- name    : QAlgorithms.Papers.Independent.Next46.P22.corollary1_comodule
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T13:39:55.195391+00:00
-- url     : https://prove2.me/theorems/eade40af-1d5d-4371-8cc1-7f34997612cd
-- title:
--   Corollary to Theorem 1 (comodule radicals)
-- statement:
--   Let $F$ be a field of characteristic zero, $H$ a finite-dimensional semisimple Hopf algebra over $F$, and $L$ a finite-dimensional right $H$-comodule Lie algebra. Its actual solvable radical $R=\operatorname{rad}(L)$ and nilpotent radical $N=\operatorname{nilrad}(L)$ are $H$-subcomodules:
--
--   $$R,N\ \text{are stable for the supplied Hopf structure}.$$
--
--   Both stability assertions are conclusions. Finite semisimplicity may equivalently be read as cosemisimplicity here. No algebraic closure of $F$ is assumed.
-- source:
--   Structure of H-(co)module Lie algebras, arXiv:1205.0778v7, PDF p. 6, Corollary to Theorem 1 (comodule radicals)

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P22

namespace QAlgorithms.Papers.Independent.Next46.P22

noncomputable section

open scoped TensorProduct

open Classical

section Statements

variable {F H L : Type*} [Field F] [Ring H] [HopfAlgebra F H] [LieRing L] [LieAlgebra F L]

/-- Comodule corollary to Theorem 1, PDF p.6: both actual radicals are subcomodules. -/
theorem corollary1_comodule [CharZero F] [FiniteDimensional F H] [IsSemisimpleRing H]
    [FiniteDimensional F L] (rho : RightComodule F H L) (hr : ComoduleLie rho) :
    CoStable rho (LieAlgebra.radical F L).toSubmodule ∧
    CoStable rho (lieNilpotentRadical F L).toSubmodule := by sorry

end Statements

end

end QAlgorithms.Papers.Independent.Next46.P22
