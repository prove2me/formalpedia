-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PSymplDetSchur_clearCol_mul_succ_26c7717bd404
-- name    : P2M_GroundTheory_Heights__Heights_PSymplDetSchur_clearCol_mul_succ_26c7717bd404
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T04:13:36.161835+00:00
-- url     : https://prove2.me/theorems/f6e105bb-f56f-5aa6-8b71-e281243b9ff5
-- title:
--   P2 M Ground Theory Heights  Heights PSympl Det Schur clear Col mul succ 26c7717bd404: P2 M Ground Theory Heights  Heights PSympl Det Schur clear Col mul succ 26c7717bd404
-- statement:
--   The P2 M Ground Theory Heights  Heights PSympl Det Schur clear Col mul succ 26c7717bd404 construction uses the P2 M Ground Theory Heights  Heights PSympl Det Schur clear Col mul succ 26c7717bd404 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PSymplDetSchur.lean#L32-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PSymplDetSchur.lean#L32-L37

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

theorem P2M_GroundTheory_Heights__Heights_PSymplDetSchur_clearCol_mul_succ_26c7717bd404 {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (i : Fin n)
    (j : Fin (n + 1)) :
    (clearCol A * A) i.succ j = A i.succ j - A i.succ 0 / A 0 0 * A 0 j := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PSymplDetSchur».«clearCol_mul_succ» := P2M_GroundTheory_Heights__Heights_PSymplDetSchur_clearCol_mul_succ_26c7717bd404
