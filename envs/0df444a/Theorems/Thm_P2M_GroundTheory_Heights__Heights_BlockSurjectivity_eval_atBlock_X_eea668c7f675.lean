-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_BlockSurjectivity_eval_atBlock_X_eea668c7f675
-- name    : P2M_GroundTheory_Heights__Heights_BlockSurjectivity_eval_atBlock_X_eea668c7f675
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T00:16:01.161861+00:00
-- url     : https://prove2.me/theorems/330b5ea0-4d89-4e5b-9717-8c0940b36c8e
-- title:
--   P2 M Ground Theory Heights  Heights Block Surjectivity eval at Block X eea668c7f675: P2 M Ground Theory Heights  Heights Block Surjectivity eval at Block X eea668c7f675
-- statement:
--   The P2 M Ground Theory Heights  Heights Block Surjectivity eval at Block X eea668c7f675 construction uses the P2 M Ground Theory Heights  Heights Block Surjectivity eval at Block X eea668c7f675 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/IsWeightedHomogeneousSepBlock.lean#L67-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/IsWeightedHomogeneousSepBlock.lean#L67-L73

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_IsWeightedHomogeneousSepBlock
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
open MvPolynomial Module
noncomputable section
open GroundTheory.Heights₂.Heights.BlockSurjectivity
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
omit [Fintype ι]

theorem P2M_GroundTheory_Heights__Heights_BlockSurjectivity_eval_atBlock_X_eea668c7f675 (k₀ : ι) (w : Cone (fun _ : Unit ↦ n k₀) ℂ) (x : Coord n → ℂ) (v : Coord n) :
    eval x (atBlock k₀ w (X v)) = withBlock k₀ (w ()) x v.1 v.2 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«BlockSurjectivity».«eval_atBlock_X» := P2M_GroundTheory_Heights__Heights_BlockSurjectivity_eval_atBlock_X_eea668c7f675
