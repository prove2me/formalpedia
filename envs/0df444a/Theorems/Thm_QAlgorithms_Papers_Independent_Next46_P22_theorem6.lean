-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P22_theorem6
-- name    : QAlgorithms.Papers.Independent.Next46.P22.theorem6
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T13:48:28.721674+00:00
-- url     : https://prove2.me/theorems/ed546958-729d-4e1c-a201-d6435fd1cbe8
-- title:
--   Theorem 6
-- statement:
--   Let $F$ have characteristic zero, $H$ be any Hopf algebra over $F$ and $L$ a finite-dimensional semisimple left $H$-module Lie algebra. There is a finite internal decomposition
--
--   $$L=B_1\oplus\cdots\oplus B_s$$
--
--   where each $B_i$ is an ideal of the ambient $L$, is invariant for the supplied Hopf structure, and is $H$-simple: every invariant Lie ideal of $B_i$ is zero or $B_i$. The simplicity test is internal to the summand. An empty family is allowed for $L=0$; no dimension or semisimplicity hypothesis on $H$ is used.
-- source:
--   Structure of H-(co)module Lie algebras, arXiv:1205.0778v7, PDF p. 11, Theorem 6

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P22

namespace QAlgorithms.Papers.Independent.Next46.P22

noncomputable section

open scoped TensorProduct

open Classical

section Statements

variable {F H L : Type*} [Field F] [Ring H] [HopfAlgebra F H] [LieRing L] [LieAlgebra F L]

variable {V W : Type*} [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]

/-- Theorem 6, PDF pp.11–12: ambient ideals simple under restricted H-action.
H is arbitrary; an empty family is allowed at L=0. -/
theorem theorem6 [CharZero F] [FiniteDimensional F L]
    (hL : Semisimple F L) (alpha : H →ₐ[F] Module.End F L) (ha : ModuleLie alpha) :
    SimpleIdealDecomposition (ActionStable alpha) := by sorry

end Statements

end

end QAlgorithms.Papers.Independent.Next46.P22
