-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P22_corollary8
-- name    : QAlgorithms.Papers.Independent.Next46.P22.corollary8
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T13:50:52.492278+00:00
-- url     : https://prove2.me/theorems/ad18e8a6-f848-4b72-bda1-fd71fcaea440
-- title:
--   Corollary to Theorem 8
-- statement:
--   Let $F$ have characteristic zero, $H$ be a Hopf algebra with a normalized ad-invariant left integral, and $L$ a finite-dimensional semisimple right $H$-comodule Lie algebra. Every finite-dimensional compatible $(H,L)$-module $V$ admits
--
--   $$V=V_1\oplus\cdots\oplus V_s$$
--
--   with irreducible simultaneous $L$-submodules and $H$-subcomodules $V_i$. Ordinary complete reducibility is not assumed. The sum is internal and finite; the index set may be empty when $V=0$. Irreducibility means that every $L$-invariant subspace of a summand that also preserves the additional structure is zero or the whole summand.
-- source:
--   Structure of H-(co)module Lie algebras, arXiv:1205.0778v7, PDF p. 13, Corollary to Theorem 8

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P22

namespace QAlgorithms.Papers.Independent.Next46.P22

noncomputable section

open scoped TensorProduct

open Classical

section Statements

variable {F H L : Type*} [Field F] [Ring H] [HopfAlgebra F H] [LieRing L] [LieAlgebra F L]

variable {V W : Type*} [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]

section LieModules

variable [LieRingModule L V] [LieModule F L V] [LieRingModule L W] [LieModule F L W]

/-- Corollary to Theorem 8, PDF p.13: ordinary complete reducibility is not assumed. -/
theorem corollary8 [CharZero F] [FiniteDimensional F L] [FiniteDimensional F V]
    (hL : Semisimple F L) (rhoL : RightComodule F H L) (hr : ComoduleLie rhoL)
    (rhoV : RightComodule F H V) (hV : CoCompatible rhoL rhoV)
    (t : H →ₗ[F] F) (ht : NormalizedAdIntegral t) :
    IrreducibleDecomposition (L := L) (CoStable rhoV) := by sorry

end LieModules

end Statements

end

end QAlgorithms.Papers.Independent.Next46.P22
