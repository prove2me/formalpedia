-- Prove2me | Theorems.Thm_P2M_GlobalTheory_pic_groupAlgebra_of_isIntegrallyClosed__4f9bdb8fe068
-- name    : P2M_GlobalTheory_pic_groupAlgebra_of_isIntegrallyClosed__4f9bdb8fe068
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:23:22.286296+00:00
-- url     : https://prove2.me/theorems/8b1dddd2-e203-42d3-b801-1a71b6a20c68
-- title:
--   P2 M Global Theory pic group Algebra of is Integrally Closed  4f9bdb8fe068: P2 M Global Theory pic group Algebra of is Integrally Closed  4f9bdb8fe068
-- statement:
--   The P2 M Global Theory pic group Algebra of is Integrally Closed  4f9bdb8fe068 construction uses the P2 M Global Theory pic group Algebra of is Integrally Closed  4f9bdb8fe068 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/UniqueFactorizationMonoidAddMonoidAlgebraOfFree.lean#L296-L314
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/UniqueFactorizationMonoidAddMonoidAlgebraOfFree.lean#L296-L314

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_UniqueFactorizationMonoidAddMonoidAlgebraOfFree
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct AlgebraMonoidAlgebra
open AddMonoidAlgebra CommRing
open GlobalTheory

theorem P2M_GlobalTheory_pic_groupAlgebra_of_isIntegrallyClosed__4f9bdb8fe068.{u, v, w} (A : Type u) [CommRing A] [IsDomain A]
    [IsIntegrallyClosed A] (X : Type v) [AddCommGroup X] [Module.Free ℤ X] :
    Function.Bijective (Pic.mapAlgebra A (AddMonoidAlgebra A X)) ∧
    (∀ (N : Type w) [AddCommGroup N] [Module (AddMonoidAlgebra A X) N]
      [Module.Invertible (AddMonoidAlgebra A X) N],
      ∃ (M : Type u) (_ : AddCommGroup M) (_ : Module A M), Module.Invertible A M ∧
        Nonempty (N ≃ₗ[AddMonoidAlgebra A X] AddMonoidAlgebra A X ⊗[A] M)) ∧
    (∀ (M M' : Type w) [AddCommGroup M] [Module A M] [Module.Invertible A M] [AddCommGroup M']
      [Module A M'] [Module.Invertible A M'],
      Nonempty (AddMonoidAlgebra A X ⊗[A] M ≃ₗ[AddMonoidAlgebra A X]
        AddMonoidAlgebra A X ⊗[A] M') → Nonempty (M ≃ₗ[A] M')) := by sorry

alias «GlobalTheory».«pic_groupAlgebra_of_isIntegrallyClosed».«» := P2M_GlobalTheory_pic_groupAlgebra_of_isIntegrallyClosed__4f9bdb8fe068
