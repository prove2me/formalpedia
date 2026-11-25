-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_PrimitiveLinearForm_exists_linear_primitive_67c803d2091d
-- name    : P2M_GroundTheory_Heights__Heights_ComplexSets_PrimitiveLinearForm_exists_linear_primitive_67c803d2091d
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T03:16:10.401284+00:00
-- url     : https://prove2.me/theorems/ccc216ba-8c3e-4c37-a648-6205b646728d
-- title:
--   P2 M Ground Theory Heights  Heights Complex Sets Primitive Linear Form exists linear primitive 67c803d2091d: P2 M Ground Theory Heights  Heights Complex Sets Primitive Linear Form exists linear primit
-- statement:
--   The P2 M Ground Theory Heights  Heights Complex Sets Primitive Linear Form exists linear primitive 67c803d2091d construction uses the P2 M Ground Theory Heights  Heights Complex Sets Primitive Linear Form exists linear primitive 67c803d2091d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PrimitiveLinearForm.lean#L26-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PrimitiveLinearForm.lean#L26-L73

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

theorem P2M_GroundTheory_Heights__Heights_ComplexSets_PrimitiveLinearForm_exists_linear_primitive_67c803d2091d {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L] {n : ℕ} (ι : ℂ →+* K) (x : Fin n → L)
    (hx : ∀ φ ψ : L →ₐ[K] AlgebraicClosure K, (∀ j, φ (x j) = ψ (x j)) → φ = ψ) :
    ∃ c : Fin n → ℂ, IntermediateField.adjoin K {∑ j, algebraMap K L (ι (c j)) * x j} = ⊤ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ComplexSets».«PrimitiveLinearForm».«exists_linear_primitive» := P2M_GroundTheory_Heights__Heights_ComplexSets_PrimitiveLinearForm_exists_linear_primitive_67c803d2091d
