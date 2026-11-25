-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowlaSelberg_eq_of_map_eq_3855758b774b
-- name    : P2M_GroundTheory_Heights__Heights_ChowlaSelberg_eq_of_map_eq_3855758b774b
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T13:08:28.498906+00:00
-- url     : https://prove2.me/theorems/0181e878-f3b2-5767-a40b-391b842bd99e
-- title:
--   P2 M Ground Theory Heights  Heights Chowla Selberg eq of map eq 3855758b774b: P2 M Ground Theory Heights  Heights Chowla Selberg eq of map eq 3855758b774b
-- statement:
--   The P2 M Ground Theory Heights  Heights Chowla Selberg eq of map eq 3855758b774b construction uses the P2 M Ground Theory Heights  Heights Chowla Selberg eq of map eq 3855758b774b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowlaSelberg/PWIdealField.lean#L52-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowlaSelberg/PWIdealField.lean#L52-L61

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

theorem P2M_GroundTheory_Heights__Heights_ChowlaSelberg_eq_of_map_eq_3855758b774b {F F' : Type*} [Field F] [NumberField F] [Field F'] [NumberField F']
    (j : F →+* F') {A B : Ideal (𝓞 F)} (hB : B ≠ ⊥)
    (h : A.map (RingOfIntegers.mapRingHom j) = B.map (RingOfIntegers.mapRingHom j)) : A = B := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChowlaSelberg».«eq_of_map_eq» := P2M_GroundTheory_Heights__Heights_ChowlaSelberg_eq_of_map_eq_3855758b774b
