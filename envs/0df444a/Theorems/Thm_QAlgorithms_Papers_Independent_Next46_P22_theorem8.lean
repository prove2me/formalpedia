-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P22_theorem8
-- name    : QAlgorithms.Papers.Independent.Next46.P22.theorem8
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T13:49:35.366744+00:00
-- url     : https://prove2.me/theorems/eaa24d01-48e7-4f52-a58f-ea068f3a55ac
-- title:
--   Theorem 8
-- statement:
--   Let $F$ have characteristic zero, $H$ be a Hopf algebra with a normalized ad-invariant left integral, and $L$ a right $H$-comodule Lie algebra. Let $V$ be a finite-dimensional compatible $(H,L)$-module that is completely reducible as an ordinary $L$-module after forgetting the coaction. There are irreducible simultaneous $L$-submodules and $H$-subcomodules $V_i$ with
--
--   $$V=V_1\oplus\cdots\oplus V_s.$$
--
--   No finite-dimensionality or semisimplicity assumption on $L$ is made. The sum is internal and finite; the index set may be empty when $V=0$. Irreducibility means that every $L$-invariant subspace of a summand that also preserves the additional structure is zero or the whole summand.
-- source:
--   Structure of H-(co)module Lie algebras, arXiv:1205.0778v7, PDF p. 12, Theorem 8

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

/-- Theorem 8, PDF p.12: underlying complete reducibility retained; L need not
be finite dimensional or semisimple. Empty sum allowed for zero V. -/
theorem theorem8 [CharZero F] [FiniteDimensional F V]
    (rhoL : RightComodule F H L) (hr : ComoduleLie rhoL)
    (rhoV : RightComodule F H V) (hV : CoCompatible rhoL rhoV)
    (t : H →ₗ[F] F) (ht : NormalizedAdIntegral t)
    (hcr : CompletelyReducible F L V) :
    IrreducibleDecomposition (L := L) (CoStable rhoV) := by sorry

end LieModules

end Statements

end

end QAlgorithms.Papers.Independent.Next46.P22
