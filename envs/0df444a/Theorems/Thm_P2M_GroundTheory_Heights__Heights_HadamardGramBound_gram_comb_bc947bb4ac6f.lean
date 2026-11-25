-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HadamardGramBound_gram_comb_bc947bb4ac6f
-- name    : P2M_GroundTheory_Heights__Heights_HadamardGramBound_gram_comb_bc947bb4ac6f
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T03:18:21.968232+00:00
-- url     : https://prove2.me/theorems/8965968b-77b0-404e-8ce0-0b224c5e0d68
-- title:
--   P2 M Ground Theory Heights  Heights Hadamard Gram Bound gram comb bc947bb4ac6f: P2 M Ground Theory Heights  Heights Hadamard Gram Bound gram comb bc947bb4ac6f
-- statement:
--   The P2 M Ground Theory Heights  Heights Hadamard Gram Bound gram comb bc947bb4ac6f construction uses the P2 M Ground Theory Heights  Heights Hadamard Gram Bound gram comb bc947bb4ac6f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/DetGramLeProdNormSq.lean#L34-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/DetGramLeProdNormSq.lean#L34-L40

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

theorem P2M_GroundTheory_Heights__Heights_HadamardGramBound_gram_comb_bc947bb4ac6f {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {r : ℕ}
    (M : Matrix (Fin r) (Fin r) ℝ) (b : Fin r → V) :
    Matrix.gram ℝ (fun i => ∑ j, M i j • b j) = M * Matrix.gram ℝ b * M.transpose := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HadamardGramBound».«gram_comb» := P2M_GroundTheory_Heights__Heights_HadamardGramBound_gram_comb_bc947bb4ac6f
