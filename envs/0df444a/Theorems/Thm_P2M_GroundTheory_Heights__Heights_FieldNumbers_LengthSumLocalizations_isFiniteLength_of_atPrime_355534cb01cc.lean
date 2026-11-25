-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_LengthSumLocalizations_isFiniteLength_of_atPrime_355534cb01cc
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_LengthSumLocalizations_isFiniteLength_of_atPrime_355534cb01cc
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:16:32.136278+00:00
-- url     : https://prove2.me/theorems/79327e70-53ca-5c45-950f-5e48142261e1
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers Length Sum Localizations is Finite Length of at Prime 355534cb01cc: P2 M Ground Theory Heights  Heights Field Numbers Length Sum Localizations is Fini
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers Length Sum Localizations is Finite Length of at Prime 355534cb01cc construction uses the P2 M Ground Theory Heights  Heights Field Numbers Length Sum Localizations is Finite Length of at Prime 355534cb01cc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/LengthSumLocalizations.lean#L33-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/LengthSumLocalizations.lean#L33-L50

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

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_LengthSumLocalizations_isFiniteLength_of_atPrime_355534cb01cc (𝔪 : Ideal B) [𝔪.IsMaximal] (C : Type*) [CommRing C]
    [Algebra B C] [IsLocalization.AtPrime C 𝔪] (M : Type*) [AddCommGroup M] [Module C M]
    [instB : Module B M] [instT : IsScalarTower B C M] (hM : IsFiniteLength C M) :
    IsFiniteLength B M := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«LengthSumLocalizations».«isFiniteLength_of_atPrime» := P2M_GroundTheory_Heights__Heights_FieldNumbers_LengthSumLocalizations_isFiniteLength_of_atPrime_355534cb01cc
