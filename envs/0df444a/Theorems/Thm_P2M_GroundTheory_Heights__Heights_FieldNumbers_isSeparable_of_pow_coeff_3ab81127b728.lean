-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_isSeparable_of_pow_coeff_3ab81127b728
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_isSeparable_of_pow_coeff_3ab81127b728
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:17:33.614281+00:00
-- url     : https://prove2.me/theorems/92e1502a-7be2-4f35-af8c-4a17bfd0bf25
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers is Separable of pow coeff 3ab81127b728: P2 M Ground Theory Heights  Heights Field Numbers is Separable of pow coeff 3ab81127b728
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers is Separable of pow coeff 3ab81127b728 construction uses the P2 M Ground Theory Heights  Heights Field Numbers is Separable of pow coeff 3ab81127b728 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/NoetherCharPLemmas.lean#L63-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/NoetherCharPLemmas.lean#L63-L87

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

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_isSeparable_of_pow_coeff_3ab81127b728 {F F' Ω : Type*} [Field F] [Field F'] [Field Ω] [Algebra F Ω]
    [Algebra F' Ω] (p : ℕ) [Fact p.Prime] [CharP Ω p] (e : ℕ) (g : F[X]) (hg : g.Separable)
    (ω : Ω) (hω : aeval (ω ^ p ^ e) g = 0)
    (hc : ∀ i, ∃ d : F', algebraMap F' Ω d ^ p ^ e = algebraMap F Ω (g.coeff i)) :
    IsSeparable F' ω := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«isSeparable_of_pow_coeff» := P2M_GroundTheory_Heights__Heights_FieldNumbers_isSeparable_of_pow_coeff_3ab81127b728
