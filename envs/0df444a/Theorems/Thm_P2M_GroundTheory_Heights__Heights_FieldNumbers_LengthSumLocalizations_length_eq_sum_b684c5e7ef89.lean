-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_LengthSumLocalizations_length_eq_sum_b684c5e7ef89
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_LengthSumLocalizations_length_eq_sum_b684c5e7ef89
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:16:49.823987+00:00
-- url     : https://prove2.me/theorems/1c32459d-f7ed-441e-ad5e-afcf806e576d
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers Length Sum Localizations length eq sum b684c5e7ef89: P2 M Ground Theory Heights  Heights Field Numbers Length Sum Localizations length eq sum b684c5e7
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers Length Sum Localizations length eq sum b684c5e7ef89 construction uses the P2 M Ground Theory Heights  Heights Field Numbers Length Sum Localizations length eq sum b684c5e7ef89 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/LengthSumLocalizations.lean#L131-L162
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/LengthSumLocalizations.lean#L131-L162

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

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_LengthSumLocalizations_length_eq_sum_b684c5e7ef89 (hinj : Function.Injective 𝔪)
    (hall : ∀ M : Ideal B, M.IsMaximal → ∃ i, M = 𝔪 i) (A : Type*) [CommRing A] [Algebra A B]
    (N : Type*) [AddCommGroup N] [Module B N] [Module A N] [IsScalarTower A B N] :
    Module.length A N = ∑ i, Module.length (C i) (C i ⊗[B] N) * Module.length A (B ⧸ 𝔪 i) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«LengthSumLocalizations».«length_eq_sum» := P2M_GroundTheory_Heights__Heights_FieldNumbers_LengthSumLocalizations_length_eq_sum_b684c5e7ef89
