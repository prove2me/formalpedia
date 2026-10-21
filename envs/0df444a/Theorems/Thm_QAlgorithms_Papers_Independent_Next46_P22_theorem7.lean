-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P22_theorem7
-- name    : QAlgorithms.Papers.Independent.Next46.P22.theorem7
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T13:49:14.685377+00:00
-- url     : https://prove2.me/theorems/7ce9d84a-7d2e-4592-95bb-d6beda1ac2e1
-- title:
--   Theorem 7
-- statement:
--   Let $F$ have characteristic zero, $H$ be any Hopf algebra over $F$ and $L$ a finite-dimensional semisimple right $H$-comodule Lie algebra. There is a finite internal decomposition
--
--   $$L=B_1\oplus\cdots\oplus B_s$$
--
--   where each $B_i$ is an ideal of the ambient $L$, is invariant for the supplied Hopf structure, and is $H$-simple: every invariant Lie ideal of $B_i$ is zero or $B_i$. The simplicity test is internal to the summand. An empty family is allowed for $L=0$; no dimension or semisimplicity hypothesis on $H$ is used.
-- source:
--   Structure of H-(co)module Lie algebras, arXiv:1205.0778v7, PDF p. 12, Theorem 7

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P22

namespace QAlgorithms.Papers.Independent.Next46.P22

noncomputable section

open scoped TensorProduct

open Classical

section Statements

variable {F H L : Type*} [Field F] [Ring H] [HopfAlgebra F H] [LieRing L] [LieAlgebra F L]

variable {V W : Type*} [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]

/-- Theorem 7, PDF p.12: ambient ideals simple under restricted H-coaction. -/
theorem theorem7 [CharZero F] [FiniteDimensional F L]
    (hL : Semisimple F L) (rho : RightComodule F H L) (hr : ComoduleLie rho) :
    SimpleIdealDecomposition (CoStable rho) := by sorry

end Statements

end

end QAlgorithms.Papers.Independent.Next46.P22
