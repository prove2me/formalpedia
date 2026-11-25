-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_BlockSurjectivity_evalBlock_apply_ca2f47e524b2
-- name    : P2M_GroundTheory_Heights__Heights_BlockSurjectivity_evalBlock_apply_ca2f47e524b2
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T00:15:48.010381+00:00
-- url     : https://prove2.me/theorems/6bdb5ddc-fad2-448b-a3ce-b7bfd02469bb
-- title:
--   P2 M Ground Theory Heights  Heights Block Surjectivity eval Block apply ca2f47e524b2: P2 M Ground Theory Heights  Heights Block Surjectivity eval Block apply ca2f47e524b2
-- statement:
--   The P2 M Ground Theory Heights  Heights Block Surjectivity eval Block apply ca2f47e524b2 construction uses the P2 M Ground Theory Heights  Heights Block Surjectivity eval Block apply ca2f47e524b2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/IsWeightedHomogeneousSepBlock.lean#L42-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/IsWeightedHomogeneousSepBlock.lean#L42-L43

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
omit [Fintype ι] [DecidableEq ι]

theorem P2M_GroundTheory_Heights__Heights_BlockSurjectivity_evalBlock_apply_ca2f47e524b2 {k₀ : ι} (w : Cone (fun _ : Unit ↦ n k₀) ℂ) (f : BlockRing n k₀) :
    evalBlock w f = evalCone w f := by sorry

alias «GroundTheory».«Heights₂».«Heights».«BlockSurjectivity».«evalBlock_apply» := P2M_GroundTheory_Heights__Heights_BlockSurjectivity_evalBlock_apply_ca2f47e524b2
