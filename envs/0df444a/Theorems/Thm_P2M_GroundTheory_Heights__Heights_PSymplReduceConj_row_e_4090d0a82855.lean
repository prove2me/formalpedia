-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PSymplReduceConj_row_e_4090d0a82855
-- name    : P2M_GroundTheory_Heights__Heights_PSymplReduceConj_row_e_4090d0a82855
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T04:14:19.501834+00:00
-- url     : https://prove2.me/theorems/8766f776-d0c9-4031-a8c2-0c35a8876353
-- title:
--   P2 M Ground Theory Heights  Heights PSympl Reduce Conj row e 4090d0a82855: P2 M Ground Theory Heights  Heights PSympl Reduce Conj row e 4090d0a82855
-- statement:
--   The P2 M Ground Theory Heights  Heights PSympl Reduce Conj row e 4090d0a82855 construction uses the P2 M Ground Theory Heights  Heights PSympl Reduce Conj row e 4090d0a82855 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PSymplReduceConj.lean#L18-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PSymplReduceConj.lean#L18-L20

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

theorem P2M_GroundTheory_Heights__Heights_PSymplReduceConj_row_e_4090d0a82855 {n : ℕ} (Q : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) :
    symplExt (1 : ℝ) 0 0 1 Q (Sum.inl 0) = symplCons 1 0 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PSymplReduceConj».«row_e» := P2M_GroundTheory_Heights__Heights_PSymplReduceConj_row_e_4090d0a82855
