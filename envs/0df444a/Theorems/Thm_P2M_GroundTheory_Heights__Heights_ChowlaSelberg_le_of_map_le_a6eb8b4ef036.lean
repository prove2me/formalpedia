-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowlaSelberg_le_of_map_le_a6eb8b4ef036
-- name    : P2M_GroundTheory_Heights__Heights_ChowlaSelberg_le_of_map_le_a6eb8b4ef036
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:16:06.71941+00:00
-- url     : https://prove2.me/theorems/cbcb9f0d-d6c5-52e2-9d5b-a0531c122481
-- title:
--   P2 M Ground Theory Heights  Heights Chowla Selberg le of map le a6eb8b4ef036: P2 M Ground Theory Heights  Heights Chowla Selberg le of map le a6eb8b4ef036
-- statement:
--   The P2 M Ground Theory Heights  Heights Chowla Selberg le of map le a6eb8b4ef036 construction uses the P2 M Ground Theory Heights  Heights Chowla Selberg le of map le a6eb8b4ef036 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowlaSelberg/PWIdealField.lean#L14-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowlaSelberg/PWIdealField.lean#L14-L50

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

theorem P2M_GroundTheory_Heights__Heights_ChowlaSelberg_le_of_map_le_a6eb8b4ef036 {F F' : Type*} [Field F] [NumberField F] [Field F'] [NumberField F']
    (j : F →+* F') {A B : Ideal (𝓞 F)} (hB : B ≠ ⊥)
    (h : A.map (RingOfIntegers.mapRingHom j) ≤ B.map (RingOfIntegers.mapRingHom j)) : A ≤ B := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChowlaSelberg».«le_of_map_le» := P2M_GroundTheory_Heights__Heights_ChowlaSelberg_le_of_map_le_a6eb8b4ef036
