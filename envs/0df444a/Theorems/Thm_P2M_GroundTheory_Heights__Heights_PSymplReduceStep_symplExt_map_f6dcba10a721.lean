-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PSymplReduceStep_symplExt_map_f6dcba10a721
-- name    : P2M_GroundTheory_Heights__Heights_PSymplReduceStep_symplExt_map_f6dcba10a721
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T04:14:11.487887+00:00
-- url     : https://prove2.me/theorems/929505a5-1314-4a43-b111-755e3a8fa671
-- title:
--   P2 M Ground Theory Heights  Heights PSympl Reduce Step sympl Ext map f6dcba10a721: P2 M Ground Theory Heights  Heights PSympl Reduce Step sympl Ext map f6dcba10a721
-- statement:
--   The P2 M Ground Theory Heights  Heights PSympl Reduce Step sympl Ext map f6dcba10a721 construction uses the P2 M Ground Theory Heights  Heights PSympl Reduce Step sympl Ext map f6dcba10a721 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PSymplReduceStep.lean#L13-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PSymplReduceStep.lean#L13-L18

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsSympl
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PSymplReduceStep
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
noncomputable section
open GroundTheory.Heights₂.Heights.PSymplReduceStep

theorem P2M_GroundTheory_Heights__Heights_PSymplReduceStep_symplExt_map_f6dcba10a721 {n : ℕ} (Q : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℤ) :
    (symplExt (1 : ℤ) 0 0 1 Q).map (Int.cast : ℤ → ℝ) =
      symplExt 1 0 0 1 (Q.map (Int.cast : ℤ → ℝ)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PSymplReduceStep».«symplExt_map» := P2M_GroundTheory_Heights__Heights_PSymplReduceStep_symplExt_map_f6dcba10a721
