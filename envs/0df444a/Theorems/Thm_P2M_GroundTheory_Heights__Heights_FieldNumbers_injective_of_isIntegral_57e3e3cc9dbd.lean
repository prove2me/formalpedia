-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_injective_of_isIntegral_57e3e3cc9dbd
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_injective_of_isIntegral_57e3e3cc9dbd
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:17:20.272801+00:00
-- url     : https://prove2.me/theorems/81980083-fecb-4c11-977e-7c8cd43f8c57
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers injective of is Integral 57e3e3cc9dbd: P2 M Ground Theory Heights  Heights Field Numbers injective of is Integral 57e3e3cc9dbd
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers injective of is Integral 57e3e3cc9dbd construction uses the P2 M Ground Theory Heights  Heights Field Numbers injective of is Integral 57e3e3cc9dbd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/NoetherCharPLemmas.lean#L54-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/NoetherCharPLemmas.lean#L54-L61

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_NoetherCharPLemmas
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
open Polynomial

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_injective_of_isIntegral_57e3e3cc9dbd {B B' Ω : Type*} [CommRing B] [Nontrivial B] [CommRing B']
    [IsDomain B'] [CommRing Ω] [Algebra B B'] [Algebra.IsIntegral B B'] (ψ : B' →+* Ω)
    (h : Function.Injective (ψ.comp (algebraMap B B'))) : Function.Injective ψ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«injective_of_isIntegral» := P2M_GroundTheory_Heights__Heights_FieldNumbers_injective_of_isIntegral_57e3e3cc9dbd
