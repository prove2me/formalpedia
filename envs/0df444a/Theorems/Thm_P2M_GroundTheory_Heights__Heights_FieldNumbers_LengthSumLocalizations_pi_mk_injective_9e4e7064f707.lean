-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_LengthSumLocalizations_pi_mk_injective_9e4e7064f707
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_LengthSumLocalizations_pi_mk_injective_9e4e7064f707
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:16:59.799182+00:00
-- url     : https://prove2.me/theorems/36c5bdf2-80d4-4c68-9d70-5c9a6f18ed68
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers Length Sum Localizations pi mk injective 9e4e7064f707: P2 M Ground Theory Heights  Heights Field Numbers Length Sum Localizations pi mk injective 9e4e
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers Length Sum Localizations pi mk injective 9e4e7064f707 construction uses the P2 M Ground Theory Heights  Heights Field Numbers Length Sum Localizations pi mk injective 9e4e7064f707 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/LengthSumLocalizations.lean#L79-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/LengthSumLocalizations.lean#L79-L98

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
omit [Fintype ι] [DecidableEq ι]

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_LengthSumLocalizations_pi_mk_injective_9e4e7064f707 (hall : ∀ M : Ideal B, M.IsMaximal → ∃ i, M = 𝔪 i) (N : Type*)
    [AddCommGroup N] [Module B N] :
    Function.Injective (LinearMap.pi fun i => TensorProduct.mk B (C i) N 1) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«LengthSumLocalizations».«pi_mk_injective» := P2M_GroundTheory_Heights__Heights_FieldNumbers_LengthSumLocalizations_pi_mk_injective_9e4e7064f707
