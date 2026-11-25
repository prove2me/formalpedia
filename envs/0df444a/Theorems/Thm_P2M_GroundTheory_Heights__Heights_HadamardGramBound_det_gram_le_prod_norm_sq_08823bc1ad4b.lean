-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HadamardGramBound_det_gram_le_prod_norm_sq_08823bc1ad4b
-- name    : P2M_GroundTheory_Heights__Heights_HadamardGramBound_det_gram_le_prod_norm_sq_08823bc1ad4b
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T03:19:00.688039+00:00
-- url     : https://prove2.me/theorems/fb0476cf-1b44-4fde-870b-18cfe70d9342
-- title:
--   P2 M Ground Theory Heights  Heights Hadamard Gram Bound det gram le prod norm sq 08823bc1ad4b: P2 M Ground Theory Heights  Heights Hadamard Gram Bound det gram le prod norm sq 08823bc1ad4b
-- statement:
--   The P2 M Ground Theory Heights  Heights Hadamard Gram Bound det gram le prod norm sq 08823bc1ad4b construction uses the P2 M Ground Theory Heights  Heights Hadamard Gram Bound det gram le prod norm sq 08823bc1ad4b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/DetGramLeProdNormSq.lean#L9-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/DetGramLeProdNormSq.lean#L9-L32

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_DetGramLeProdNormSq
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
open GroundTheory.Heights₂.Heights.HadamardGramBound

theorem P2M_GroundTheory_Heights__Heights_HadamardGramBound_det_gram_le_prod_norm_sq_08823bc1ad4b {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {n : ℕ} (w : Fin n → V) (hw : LinearIndependent ℝ w) :
    (Matrix.gram ℝ w).det ≤ ∏ i, ‖w i‖ ^ 2 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HadamardGramBound».«det_gram_le_prod_norm_sq» := P2M_GroundTheory_Heights__Heights_HadamardGramBound_det_gram_le_prod_norm_sq_08823bc1ad4b
