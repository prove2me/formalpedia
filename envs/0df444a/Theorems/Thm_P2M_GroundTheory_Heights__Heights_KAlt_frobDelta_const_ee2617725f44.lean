-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_KAlt_frobDelta_const_ee2617725f44
-- name    : P2M_GroundTheory_Heights__Heights_KAlt_frobDelta_const_ee2617725f44
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:24:39.400836+00:00
-- url     : https://prove2.me/theorems/1ba549e4-ceb4-4957-94e3-e69c2888c8dc
-- title:
--   P2 M Ground Theory Heights  Heights KAlt frob Delta const ee2617725f44: P2 M Ground Theory Heights  Heights KAlt frob Delta const ee2617725f44
-- statement:
--   The P2 M Ground Theory Heights  Heights KAlt frob Delta const ee2617725f44 construction uses the P2 M Ground Theory Heights  Heights KAlt frob Delta const ee2617725f44 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/AltFrob.lean#L60-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/AltFrob.lean#L60-L73

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

theorem P2M_GroundTheory_Heights__Heights_KAlt_frobDelta_const_ee2617725f44 {r : ℕ} (s : ℕ) :
    frobDelta (fun _ : Fin r => s) = ∏ a : Fin r, (((r - 1 - (a : ℕ)).factorial : ℕ) : ℚ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«KAlt».«frobDelta_const» := P2M_GroundTheory_Heights__Heights_KAlt_frobDelta_const_ee2617725f44
