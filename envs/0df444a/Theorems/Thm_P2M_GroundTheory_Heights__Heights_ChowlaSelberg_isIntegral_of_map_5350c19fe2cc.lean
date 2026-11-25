-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowlaSelberg_isIntegral_of_map_5350c19fe2cc
-- name    : P2M_GroundTheory_Heights__Heights_ChowlaSelberg_isIntegral_of_map_5350c19fe2cc
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:16:00.793799+00:00
-- url     : https://prove2.me/theorems/f14e51e9-29a8-5540-819e-ea4ae5f63745
-- title:
--   P2 M Ground Theory Heights  Heights Chowla Selberg is Integral of map 5350c19fe2cc: P2 M Ground Theory Heights  Heights Chowla Selberg is Integral of map 5350c19fe2cc
-- statement:
--   The P2 M Ground Theory Heights  Heights Chowla Selberg is Integral of map 5350c19fe2cc construction uses the P2 M Ground Theory Heights  Heights Chowla Selberg is Integral of map 5350c19fe2cc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowlaSelberg/PWIdealField.lean#L10-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowlaSelberg/PWIdealField.lean#L10-L12

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

theorem P2M_GroundTheory_Heights__Heights_ChowlaSelberg_isIntegral_of_map_5350c19fe2cc {F F' : Type*} [Field F] [Field F'] (j : F →+* F') {x : F}
    (h : IsIntegral ℤ (j x)) : IsIntegral ℤ x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChowlaSelberg».«isIntegral_of_map» := P2M_GroundTheory_Heights__Heights_ChowlaSelberg_isIntegral_of_map_5350c19fe2cc
