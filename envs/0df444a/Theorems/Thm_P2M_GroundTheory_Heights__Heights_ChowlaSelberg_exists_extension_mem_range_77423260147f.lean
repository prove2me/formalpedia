-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowlaSelberg_exists_extension_mem_range_77423260147f
-- name    : P2M_GroundTheory_Heights__Heights_ChowlaSelberg_exists_extension_mem_range_77423260147f
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T13:08:40.45292+00:00
-- url     : https://prove2.me/theorems/a787a111-0b6e-4325-a468-45e4a3a20a1e
-- title:
--   P2 M Ground Theory Heights  Heights Chowla Selberg exists extension mem range 77423260147f: P2 M Ground Theory Heights  Heights Chowla Selberg exists extension mem range 77423260147f
-- statement:
--   The P2 M Ground Theory Heights  Heights Chowla Selberg exists extension mem range 77423260147f construction uses the P2 M Ground Theory Heights  Heights Chowla Selberg exists extension mem range 77423260147f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowlaSelberg/PWIdealField.lean#L63-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowlaSelberg/PWIdealField.lean#L63-L83

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowlaSelberg_PWIdealField
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.ChowlaSelberg
open NumberField
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_ChowlaSelberg_exists_extension_mem_range_77423260147f {F : Type} [Field F] [NumberField F] (τ : F →+* ℂ) {z₁ z₂ : ℂ}
    (h₁ : IsAlgebraic ℚ z₁) (h₂ : IsAlgebraic ℚ z₂) :
    ∃ (F' : Type) (_ : Field F') (_ : NumberField F') (j : F →+* F') (τ' : F' →+* ℂ),
      τ'.comp j = τ ∧ z₁ ∈ Set.range τ' ∧ z₂ ∈ Set.range τ' := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChowlaSelberg».«exists_extension_mem_range» := P2M_GroundTheory_Heights__Heights_ChowlaSelberg_exists_extension_mem_range_77423260147f
