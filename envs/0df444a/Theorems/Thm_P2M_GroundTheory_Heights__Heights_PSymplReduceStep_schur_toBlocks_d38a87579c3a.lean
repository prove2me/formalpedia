-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PSymplReduceStep_schur_toBlocks_d38a87579c3a
-- name    : P2M_GroundTheory_Heights__Heights_PSymplReduceStep_schur_toBlocks_d38a87579c3a
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T04:13:53.033073+00:00
-- url     : https://prove2.me/theorems/f52056d5-127a-5f0f-913d-119287146968
-- title:
--   P2 M Ground Theory Heights  Heights PSympl Reduce Step schur to Blocks d38a87579c3a: P2 M Ground Theory Heights  Heights PSympl Reduce Step schur to Blocks d38a87579c3a
-- statement:
--   The P2 M Ground Theory Heights  Heights PSympl Reduce Step schur to Blocks d38a87579c3a construction uses the P2 M Ground Theory Heights  Heights PSympl Reduce Step schur to Blocks d38a87579c3a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PSymplReduceStep.lean#L20-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PSymplReduceStep.lean#L20-L25

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

theorem P2M_GroundTheory_Heights__Heights_PSymplReduceStep_schur_toBlocks_d38a87579c3a {n : ℕ} (K : Matrix (Fin (n + 1) ⊕ Fin (n + 1)) (Fin (n + 1) ⊕ Fin (n + 1)) ℝ) :
    (Matrix.of fun i j : Fin n => K.toBlocks₁₁ i.succ j.succ -
        K.toBlocks₁₁ i.succ 0 * K.toBlocks₁₁ 0 j.succ / K.toBlocks₁₁ 0 0) =
      (symplReduce K).toBlocks₁₁ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PSymplReduceStep».«schur_toBlocks» := P2M_GroundTheory_Heights__Heights_PSymplReduceStep_schur_toBlocks_d38a87579c3a
