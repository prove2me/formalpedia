-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_finrank_eq_relfinrank_of_div_a165af8765a4
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_finrank_eq_relfinrank_of_div_a165af8765a4
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T07:54:35.903017+00:00
-- url     : https://prove2.me/theorems/64be58b0-e782-4be9-8e93-26e40cf0c47c
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers finrank eq relfinrank of div a165af8765a4: P2 M Ground Theory Heights  Heights Field Numbers finrank eq relfinrank of div a165af8765a4
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers finrank eq relfinrank of div a165af8765a4 construction uses the P2 M Ground Theory Heights  Heights Field Numbers finrank eq relfinrank of div a165af8765a4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PSemilocalFiniteRank.lean#L25-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PSemilocalFiniteRank.lean#L25-L51

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsFibreFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsSemilocalFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsDegZeroLocFrac
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PSemilocalFiniteRank
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u
variable {F L₀ L : Type*} [Field F] [Field L₀] [Field L] [Algebra F L₀] [Algebra F L]

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_finrank_eq_relfinrank_of_div_a165af8765a4 (φ : L₀ →ₐ[F] L) {K₀ : IntermediateField F L₀}
    {E : IntermediateField F L} (hKE : K₀.map φ ≤ E) {A : Subalgebra F L₀} {B : Subalgebra F L}
    [Algebra A B] (hφ : ∀ a : A, ((algebraMap A B a : B) : L) = φ a) (hA : ∀ a ∈ A, a ∈ K₀)
    (hB : ∀ b ∈ B, b ∈ E) (fracA : ∀ x ∈ K₀, ∃ y ∈ A, ∃ z ∈ A, z ≠ 0 ∧ x = y / z)
    (fracB : ∀ x ∈ E, ∃ y ∈ B, ∃ z ∈ B, z ≠ 0 ∧ x = y / z) :
    Module.finrank A B = IntermediateField.relfinrank (K₀.map φ) E := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«finrank_eq_relfinrank_of_div» := P2M_GroundTheory_Heights__Heights_FieldNumbers_finrank_eq_relfinrank_of_div_a165af8765a4
