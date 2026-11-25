-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_KAlt_frobDim_eq_c066fd4b76d0
-- name    : P2M_GroundTheory_Heights__Heights_KAlt_frobDim_eq_c066fd4b76d0
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:25:01.861039+00:00
-- url     : https://prove2.me/theorems/429e34ee-1ee2-4b7f-8eca-144ceff22a65
-- title:
--   P2 M Ground Theory Heights  Heights KAlt frob Dim eq c066fd4b76d0: P2 M Ground Theory Heights  Heights KAlt frob Dim eq c066fd4b76d0
-- statement:
--   The P2 M Ground Theory Heights  Heights KAlt frob Dim eq c066fd4b76d0 construction uses the P2 M Ground Theory Heights  Heights KAlt frob Dim eq c066fd4b76d0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/AltFrob.lean#L15-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/AltFrob.lean#L15-L17

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

theorem P2M_GroundTheory_Heights__Heights_KAlt_frobDim_eq_c066fd4b76d0 {r : ℕ} (la : Fin r → ℕ) :
    frobDim la = ((∑ a, la a).factorial : ℚ) * frobDelta la /
      ∏ a : Fin r, ((la a + (r - 1 - a)).factorial : ℚ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«KAlt».«frobDim_eq» := P2M_GroundTheory_Heights__Heights_KAlt_frobDim_eq_c066fd4b76d0
