-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_KShort_norm_lt_of_mem_cube_d47b19df4675
-- name    : P2M_GroundTheory_Heights__Heights_KShort_norm_lt_of_mem_cube_d47b19df4675
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:26:11.254742+00:00
-- url     : https://prove2.me/theorems/00099c27-bb4f-4a6f-aa43-86a6318e3e77
-- title:
--   P2 M Ground Theory Heights  Heights KShort norm lt of mem cube d47b19df4675: P2 M Ground Theory Heights  Heights KShort norm lt of mem cube d47b19df4675
-- statement:
--   The P2 M Ground Theory Heights  Heights KShort norm lt of mem cube d47b19df4675 construction uses the P2 M Ground Theory Heights  Heights KShort norm lt of mem cube d47b19df4675 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/ShortVectors.lean#L27-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/ShortVectors.lean#L27-L43

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

theorem P2M_GroundTheory_Heights__Heights_KShort_norm_lt_of_mem_cube_d47b19df4675 {n : ℕ} (hn : 0 < n) {lam : ℝ} (hlam : 0 < lam)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ cube n (lam / √n)) : ‖x‖ < lam := by sorry

alias «GroundTheory».«Heights₂».«Heights».«KShort».«norm_lt_of_mem_cube» := P2M_GroundTheory_Heights__Heights_KShort_norm_lt_of_mem_cube_d47b19df4675
