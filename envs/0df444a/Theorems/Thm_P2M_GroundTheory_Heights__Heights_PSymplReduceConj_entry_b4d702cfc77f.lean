-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PSymplReduceConj_entry_b4d702cfc77f
-- name    : P2M_GroundTheory_Heights__Heights_PSymplReduceConj_entry_b4d702cfc77f
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T04:14:00.893878+00:00
-- url     : https://prove2.me/theorems/4789f6c0-6e72-4052-b9f4-e648a825c384
-- title:
--   P2 M Ground Theory Heights  Heights PSympl Reduce Conj entry b4d702cfc77f: P2 M Ground Theory Heights  Heights PSympl Reduce Conj entry b4d702cfc77f
-- statement:
--   The P2 M Ground Theory Heights  Heights PSympl Reduce Conj entry b4d702cfc77f construction uses the P2 M Ground Theory Heights  Heights PSympl Reduce Conj entry b4d702cfc77f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PSymplReduceConj.lean#L26-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PSymplReduceConj.lean#L26-L31

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

theorem P2M_GroundTheory_Heights__Heights_PSymplReduceConj_entry_b4d702cfc77f {l : Type*} [Fintype l] (E H : Matrix l l ℝ) (x y : l) :
    (E * H * Eᵀ) x y = ∑ w, E x w * ∑ z, E y z * H w z := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PSymplReduceConj».«entry» := P2M_GroundTheory_Heights__Heights_PSymplReduceConj_entry_b4d702cfc77f
