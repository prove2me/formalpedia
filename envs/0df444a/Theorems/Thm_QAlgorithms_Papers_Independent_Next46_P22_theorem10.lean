-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P22_theorem10
-- name    : QAlgorithms.Papers.Independent.Next46.P22.theorem10
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T13:51:35.339071+00:00
-- url     : https://prove2.me/theorems/c9515bb9-ff64-4314-aaba-ff6385f8f476
-- title:
--   Theorem 10
-- statement:
--   Let $F$ have characteristic zero, $H$ be a finite-dimensional semisimple Hopf algebra, and $L$ an $H$-module Lie algebra, or separately an $H$-comodule Lie algebra. Let $V$ be a finite-dimensional compatible $(H,L)$-module that is completely reducible after forgetting its Hopf structure. Then
--
--   $$V=V_1\oplus\cdots\oplus V_s$$
--
--   for irreducible simultaneous submodules in the corresponding action or coaction sense. Compatibility uses $h(av)=\sum(h_1a)(h_2v)$ for actions, or $\rho(av)=\sum a_0v_0\otimes a_1v_1$ for coactions. Both variants are asserted; $L$ need not be finite dimensional or semisimple. The sum is internal and finite; the index set may be empty when $V=0$. Irreducibility means that every $L$-invariant subspace of a summand that also preserves the additional structure is zero or the whole summand.
-- source:
--   Structure of H-(co)module Lie algebras, arXiv:1205.0778v7, PDF p. 13, Theorem 10

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

/-- Theorem 10, PDF p.13: separately quantified module AND comodule variants;
finite semisimple H, finite V, arbitrary-dimensional L. -/
theorem theorem10 [CharZero F] [FiniteDimensional F H] [IsSemisimpleRing H]
    [FiniteDimensional F V] (hcr : CompletelyReducible F L V) :
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
