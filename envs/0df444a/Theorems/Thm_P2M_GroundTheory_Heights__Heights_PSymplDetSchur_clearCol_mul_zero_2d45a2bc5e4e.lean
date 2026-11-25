-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PSymplDetSchur_clearCol_mul_zero_2d45a2bc5e4e
-- name    : P2M_GroundTheory_Heights__Heights_PSymplDetSchur_clearCol_mul_zero_2d45a2bc5e4e
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T04:13:50.598637+00:00
-- url     : https://prove2.me/theorems/fd742365-91f9-495d-a642-4d533e5f4afe
-- title:
--   P2 M Ground Theory Heights  Heights PSympl Det Schur clear Col mul zero 2d45a2bc5e4e: P2 M Ground Theory Heights  Heights PSympl Det Schur clear Col mul zero 2d45a2bc5e4e
-- statement:
--   The P2 M Ground Theory Heights  Heights PSympl Det Schur clear Col mul zero 2d45a2bc5e4e construction uses the P2 M Ground Theory Heights  Heights PSympl Det Schur clear Col mul zero 2d45a2bc5e4e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PSymplDetSchur.lean#L27-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PSymplDetSchur.lean#L27-L30

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

theorem P2M_GroundTheory_Heights__Heights_PSymplDetSchur_clearCol_mul_zero_2d45a2bc5e4e {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (j : Fin (n + 1)) :
    (clearCol A * A) 0 j = A 0 j := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PSymplDetSchur».«clearCol_mul_zero» := P2M_GroundTheory_Heights__Heights_PSymplDetSchur_clearCol_mul_zero_2d45a2bc5e4e
