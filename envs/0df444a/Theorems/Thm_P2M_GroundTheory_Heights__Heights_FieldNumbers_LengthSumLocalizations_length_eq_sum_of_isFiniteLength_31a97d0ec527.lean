-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_LengthSumLocalizations_length_eq_sum_of_isFiniteLength_31a97d0ec527
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_LengthSumLocalizations_length_eq_sum_of_isFiniteLength_31a97d0ec527
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:16:50.42982+00:00
-- url     : https://prove2.me/theorems/cdc23288-8ff9-4abd-a34d-8783b4b8fa31
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers Length Sum Localizations length eq sum of is Finite Length 31a97d0ec527: P2 M Ground Theory Heights  Heights Field Numbers Length Sum Localizations le
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers Length Sum Localizations length eq sum of is Finite Length 31a97d0ec527 construction uses the P2 M Ground Theory Heights  Heights Field Numbers Length Sum Localizations length eq sum of is Finite Length 31a97d0ec527 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/LengthSumLocalizations.lean#L100-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/LengthSumLocalizations.lean#L100-L129

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_LengthSumLocalizations
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
open Module TensorProduct
noncomputable section
open GroundTheory.Heights₂.Heights.FieldNumbers.LengthSumLocalizations
variable {B : Type*} [CommRing B]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (𝔪 : ι → Ideal B) [h𝔪 : ∀ i, (𝔪 i).IsMaximal]
  (C : ι → Type*) [∀ i, CommRing (C i)] [∀ i, Algebra B (C i)]
  [∀ i, IsLocalization.AtPrime (C i) (𝔪 i)]

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_LengthSumLocalizations_length_eq_sum_of_isFiniteLength_31a97d0ec527 (hinj : Function.Injective 𝔪)
    (hall : ∀ M : Ideal B, M.IsMaximal → ∃ i, M = 𝔪 i) (A : Type*) [CommRing A] [Algebra A B]
    (N : Type*) [AddCommGroup N] [Module B N] [instA : Module A N] [instT : IsScalarTower A B N]
    (hN : IsFiniteLength B N) :
    Module.length A N = ∑ i, Module.length (C i) (C i ⊗[B] N) * Module.length A (B ⧸ 𝔪 i) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«LengthSumLocalizations».«length_eq_sum_of_isFiniteLength» := P2M_GroundTheory_Heights__Heights_FieldNumbers_LengthSumLocalizations_length_eq_sum_of_isFiniteLength_31a97d0ec527
