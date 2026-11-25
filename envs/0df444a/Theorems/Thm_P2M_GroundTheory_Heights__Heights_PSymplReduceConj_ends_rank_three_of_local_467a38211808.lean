-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PSymplReduceConj_ends_rank_three_of_local_467a38211808
-- name    : P2M_GroundTheory_Heights__Heights_PSymplReduceConj_ends_rank_three_of_local_467a38211808
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T04:13:50.943366+00:00
-- url     : https://prove2.me/theorems/758d1d32-9e8b-49d9-b69c-05fda82fc36b
-- title:
--   P2 M Ground Theory Heights  Heights PSympl Reduce Conj ends rank three of local 467a38211808: P2 M Ground Theory Heights  Heights PSympl Reduce Conj ends rank three of local 467a38211808
-- statement:
--   The P2 M Ground Theory Heights  Heights PSympl Reduce Conj ends rank three of local 467a38211808 construction uses the P2 M Ground Theory Heights  Heights PSympl Reduce Conj ends rank three of local 467a38211808 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PSymplReduceConj.lean#L22-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PSymplReduceConj.lean#L22-L24

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsSympl
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PSymplReduceConj
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
open GroundTheory.Heights₂.Heights.PSymplReduceConj

theorem P2M_GroundTheory_Heights__Heights_PSymplReduceConj_ends_rank_three_of_local_467a38211808 {n : ℕ} (Q : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) (a : Fin n ⊕ Fin n) :
    symplExt (1 : ℝ) 0 0 1 Q (Sum.map Fin.succ Fin.succ a) = symplCons 0 0 (Q a) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PSymplReduceConj».«ends_rank_three_of_local» := P2M_GroundTheory_Heights__Heights_PSymplReduceConj_ends_rank_three_of_local_467a38211808
