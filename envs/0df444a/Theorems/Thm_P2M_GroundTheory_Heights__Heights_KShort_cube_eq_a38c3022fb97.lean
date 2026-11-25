-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_KShort_cube_eq_a38c3022fb97
-- name    : P2M_GroundTheory_Heights__Heights_KShort_cube_eq_a38c3022fb97
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:25:53.860532+00:00
-- url     : https://prove2.me/theorems/4ca3e9bf-aed8-571e-bd7e-60add100ec69
-- title:
--   P2 M Ground Theory Heights  Heights KShort cube eq a38c3022fb97: P2 M Ground Theory Heights  Heights KShort cube eq a38c3022fb97
-- statement:
--   The P2 M Ground Theory Heights  Heights KShort cube eq a38c3022fb97 construction uses the P2 M Ground Theory Heights  Heights KShort cube eq a38c3022fb97 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/ShortVectors.lean#L15-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/ShortVectors.lean#L15-L17

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KernelsMatrix
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ShortVectors
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
open MeasureTheory Module Metric
noncomputable section
open GroundTheory.Heights₂.Heights.KShort

theorem P2M_GroundTheory_Heights__Heights_KShort_cube_eq_a38c3022fb97 (n : ℕ) (c : ℝ) :
    cube n c = (WithLp.ofLp) ⁻¹' (Set.pi Set.univ fun _ : Fin n => Set.Ioo (-c) c) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«KShort».«cube_eq» := P2M_GroundTheory_Heights__Heights_KShort_cube_eq_a38c3022fb97
