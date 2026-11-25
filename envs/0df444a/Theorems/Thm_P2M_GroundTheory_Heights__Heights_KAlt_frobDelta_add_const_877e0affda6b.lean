-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_KAlt_frobDelta_add_const_877e0affda6b
-- name    : P2M_GroundTheory_Heights__Heights_KAlt_frobDelta_add_const_877e0affda6b
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:24:47.430035+00:00
-- url     : https://prove2.me/theorems/a6e04603-22fd-4747-8d50-4f8d21f2ec91
-- title:
--   P2 M Ground Theory Heights  Heights KAlt frob Delta add const 877e0affda6b: P2 M Ground Theory Heights  Heights KAlt frob Delta add const 877e0affda6b
-- statement:
--   The P2 M Ground Theory Heights  Heights KAlt frob Delta add const 877e0affda6b construction uses the P2 M Ground Theory Heights  Heights KAlt frob Delta add const 877e0affda6b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/AltFrob.lean#L19-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/AltFrob.lean#L19-L25

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KernelsRest
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_AltFrob
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open Finset
open GroundTheory.Heights₂.Heights.KAlt

theorem P2M_GroundTheory_Heights__Heights_KAlt_frobDelta_add_const_877e0affda6b {r : ℕ} (s : ℕ) (ν : Fin r → ℕ) :
    frobDelta (fun a => s + ν a) = frobDelta ν := by sorry

alias «GroundTheory».«Heights₂».«Heights».«KAlt».«frobDelta_add_const» := P2M_GroundTheory_Heights__Heights_KAlt_frobDelta_add_const_877e0affda6b
