-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PSymplDetSchur_det_clearCol_b08499293871
-- name    : P2M_GroundTheory_Heights__Heights_PSymplDetSchur_det_clearCol_b08499293871
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T04:13:43.556796+00:00
-- url     : https://prove2.me/theorems/c1813e01-dceb-5592-9b37-79c442153621
-- title:
--   P2 M Ground Theory Heights  Heights PSympl Det Schur det clear Col b08499293871: P2 M Ground Theory Heights  Heights PSympl Det Schur det clear Col b08499293871
-- statement:
--   The P2 M Ground Theory Heights  Heights PSympl Det Schur det clear Col b08499293871 construction uses the P2 M Ground Theory Heights  Heights PSympl Det Schur det clear Col b08499293871 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PSymplDetSchur.lean#L15-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PSymplDetSchur.lean#L15-L25

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsSympl
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PSymplDetSchur
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
open GroundTheory.Heights₂.Heights.PSymplDetSchur

theorem P2M_GroundTheory_Heights__Heights_PSymplDetSchur_det_clearCol_b08499293871 {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    (clearCol A).det = 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PSymplDetSchur».«det_clearCol» := P2M_GroundTheory_Heights__Heights_PSymplDetSchur_det_clearCol_b08499293871
