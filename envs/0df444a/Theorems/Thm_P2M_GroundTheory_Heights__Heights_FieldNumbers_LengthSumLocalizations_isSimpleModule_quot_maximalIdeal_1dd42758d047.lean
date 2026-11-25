-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_LengthSumLocalizations_isSimpleModule_quot_maximalIdeal_1dd42758d047
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_LengthSumLocalizations_isSimpleModule_quot_maximalIdeal_1dd42758d047
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:16:52.823204+00:00
-- url     : https://prove2.me/theorems/ee82414f-4227-465c-9b5c-b0013b5ea040
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers Length Sum Localizations is Simple Module quot maximal Ideal 1dd42758d047: P2 M Ground Theory Heights  Heights Field Numbers Length Sum Localizations
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers Length Sum Localizations is Simple Module quot maximal Ideal 1dd42758d047 construction uses the P2 M Ground Theory Heights  Heights Field Numbers Length Sum Localizations is Simple Module quot maximal Ideal 1dd42758d047 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/LengthSumLocalizations.lean#L23-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/LengthSumLocalizations.lean#L23-L31

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

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_LengthSumLocalizations_isSimpleModule_quot_maximalIdeal_1dd42758d047 (𝔪 : Ideal B) [𝔪.IsMaximal] (C : Type*) [CommRing C]
    [Algebra B C] [IsLocalization.AtPrime C 𝔪] :
    have : IsLocalRing C := IsLocalization.AtPrime.isLocalRing C 𝔪
    IsSimpleModule B (C ⧸ IsLocalRing.maximalIdeal C) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«LengthSumLocalizations».«isSimpleModule_quot_maximalIdeal» := P2M_GroundTheory_Heights__Heights_FieldNumbers_LengthSumLocalizations_isSimpleModule_quot_maximalIdeal_1dd42758d047
