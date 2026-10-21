-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P22_corollary10
-- name    : QAlgorithms.Papers.Independent.Next46.P22.corollary10
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T13:49:56.562626+00:00
-- url     : https://prove2.me/theorems/c4e2eae7-9415-4144-a179-ea5a4f4d8313
-- title:
--   Corollary to Theorem 10
-- statement:
--   Let $F$ have characteristic zero, $H$ be a finite-dimensional semisimple Hopf algebra and $L$ a finite-dimensional semisimple $H$-module Lie algebra, or separately an $H$-comodule Lie algebra. Every finite-dimensional compatible $(H,L)$-module $V$ admits
--
--   $$V=V_1\oplus\cdots\oplus V_s$$
--
--   with irreducible simultaneous submodules for the corresponding action or coaction. Compatibility is the action or coaction identity from the $(H,L)$-module definition. Both variants are asserted, without an ordinary complete-reducibility hypothesis. The sum is internal and finite; the index set may be empty when $V=0$. Irreducibility means that every $L$-invariant subspace of a summand that also preserves the additional structure is zero or the whole summand.
-- source:
--   Structure of H-(co)module Lie algebras, arXiv:1205.0778v7, PDF p. 13, Corollary to Theorem 10

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

/-- Corollary to Theorem 10, PDF p.13: BOTH variants, no reducibility hypothesis. -/
theorem corollary10 [CharZero F] [FiniteDimensional F H] [IsSemisimpleRing H]
    [FiniteDimensional F L] [FiniteDimensional F V] (hL : Semisimple F L) :
    (∀ alphaL : H →ₐ[F] Module.End F L, ∀ alphaV : H →ₐ[F] Module.End F V,
      ModuleLie alphaL → ActionCompatible alphaL alphaV →
      IrreducibleDecomposition (L := L) (ActionStable alphaV)) ∧
    (∀ rhoL : RightComodule F H L, ∀ rhoV : RightComodule F H V,
      ComoduleLie rhoL → CoCompatible rhoL rhoV →
      IrreducibleDecomposition (L := L) (CoStable rhoV)) := by sorry

end LieModules

end Statements

end

end QAlgorithms.Papers.Independent.Next46.P22
