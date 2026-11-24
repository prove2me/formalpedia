-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_PrimitiveLinearForm_exists_primitive_data_34d085bb3e1a
-- name    : P2M_GroundTheory_Heights__Heights_ComplexSets_PrimitiveLinearForm_exists_primitive_data_34d085bb3e1a
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T00:58:24.490288+00:00
-- url     : https://prove2.me/theorems/6c84023a-83b7-46cb-b063-0d579d9c6eb7
-- title:
--   P2 M Ground Theory Heights  Heights Complex Sets Primitive Linear Form exists primitive data 34d085bb3e1a: P2 M Ground Theory Heights  Heights Complex Sets Primitive Linear Form exists primitive data
-- statement:
--   The P2 M Ground Theory Heights  Heights Complex Sets Primitive Linear Form exists primitive data 34d085bb3e1a construction uses the P2 M Ground Theory Heights  Heights Complex Sets Primitive Linear Form exists primitive data 34d085bb3e1a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PrimitiveLinearForm.lean#L75-L182
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PrimitiveLinearForm.lean#L75-L182

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PrimitiveLinearForm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.ComplexSets
open Polynomial TensorProduct
noncomputable section
open GroundTheory.Heights₂.Heights.ComplexSets.PrimitiveLinearForm
variable (R B : Type*) [CommRing R] [CommRing B] [Algebra R B]
attribute [local instance] tensorRightAlgebra

theorem P2M_GroundTheory_Heights__Heights_ComplexSets_PrimitiveLinearForm_exists_primitive_data_34d085bb3e1a {R B : Type*} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [CommRing B] [IsDomain B] [Algebra R B] [Module.Finite R B]
    (hinj : Function.Injective (algebraMap R B)) (ι : ℂ →+* R) {n : ℕ} (x : Fin n → B)
    (hx : Algebra.adjoin R (Set.range x) = ⊤) :
    ∃ (c : Fin n → ℂ) (m : R[X]) (D : R) (Q : Fin n → R[X]),
      m.Monic ∧ m.natDegree = Module.finrank (FractionRing R) (FractionRing R ⊗[R] B) ∧
      (∀ p : R[X], aeval (∑ j, algebraMap R B (ι (c j)) * x j) p = 0 ↔ m ∣ p) ∧
      D ≠ 0 ∧ (∃ a b : R[X], a * m + b * derivative m = C D) ∧
      ∀ j, algebraMap R B D * x j = aeval (∑ j, algebraMap R B (ι (c j)) * x j) (Q j) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ComplexSets».«PrimitiveLinearForm».«exists_primitive_data» := P2M_GroundTheory_Heights__Heights_ComplexSets_PrimitiveLinearForm_exists_primitive_data_34d085bb3e1a
