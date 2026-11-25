-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_LengthSumLocalizations_length_tensor_quot_434076816485
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_LengthSumLocalizations_length_tensor_quot_434076816485
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:16:37.314769+00:00
-- url     : https://prove2.me/theorems/60ca6856-8a03-5459-ab82-1173ac86eb58
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers Length Sum Localizations length tensor quot 434076816485: P2 M Ground Theory Heights  Heights Field Numbers Length Sum Localizations length tensor quo
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers Length Sum Localizations length tensor quot 434076816485 construction uses the P2 M Ground Theory Heights  Heights Field Numbers Length Sum Localizations length tensor quot 434076816485 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/LengthSumLocalizations.lean#L58-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/LengthSumLocalizations.lean#L58-L75

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
omit [Fintype ι]

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_LengthSumLocalizations_length_tensor_quot_434076816485 (hinj : Function.Injective 𝔪) (i j : ι) :
    Module.length (C i) (C i ⊗[B] (B ⧸ 𝔪 j)) = if i = j then 1 else 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«LengthSumLocalizations».«length_tensor_quot» := P2M_GroundTheory_Heights__Heights_FieldNumbers_LengthSumLocalizations_length_tensor_quot_434076816485
