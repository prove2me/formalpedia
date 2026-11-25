-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PSymplDetBound_step_bound_847aa8cffc89
-- name    : P2M_GroundTheory_Heights__Heights_PSymplDetBound_step_bound_847aa8cffc89
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T04:13:42.157531+00:00
-- url     : https://prove2.me/theorems/d00720d1-fc09-4089-a02f-aea5d45dac07
-- title:
--   P2 M Ground Theory Heights  Heights PSympl Det Bound step bound 847aa8cffc89: P2 M Ground Theory Heights  Heights PSympl Det Bound step bound 847aa8cffc89
-- statement:
--   The P2 M Ground Theory Heights  Heights PSympl Det Bound step bound 847aa8cffc89 construction uses the P2 M Ground Theory Heights  Heights PSympl Det Bound step bound 847aa8cffc89 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PSymplDetBound.lean#L11-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PSymplDetBound.lean#L11-L21

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsSympl
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PSymplDetBound
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
open Matrix
open GroundTheory.Heights₂.Heights.PSymplDetBound

theorem P2M_GroundTheory_Heights__Heights_PSymplDetBound_step_bound_847aa8cffc89 (n : ℕ) (ρ : ℝ) (hle : ρ ≤ 2 * ((n : ℝ) + 1)) :
    ρ * (2 * (n : ℝ)) ^ n ≤ (2 * ((n + 1 : ℕ) : ℝ)) ^ (n + 1) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PSymplDetBound».«step_bound» := P2M_GroundTheory_Heights__Heights_PSymplDetBound_step_bound_847aa8cffc89
