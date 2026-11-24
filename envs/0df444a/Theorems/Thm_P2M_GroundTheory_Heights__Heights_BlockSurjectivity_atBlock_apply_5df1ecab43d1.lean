-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_BlockSurjectivity_atBlock_apply_5df1ecab43d1
-- name    : P2M_GroundTheory_Heights__Heights_BlockSurjectivity_atBlock_apply_5df1ecab43d1
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:57:47.407563+00:00
-- url     : https://prove2.me/theorems/62e87a48-f2de-4c58-9b17-dbfb9092c6ed
-- title:
--   P2 M Ground Theory Heights  Heights Block Surjectivity at Block apply 5df1ecab43d1: P2 M Ground Theory Heights  Heights Block Surjectivity at Block apply 5df1ecab43d1
-- statement:
--   The P2 M Ground Theory Heights  Heights Block Surjectivity at Block apply 5df1ecab43d1 construction uses the P2 M Ground Theory Heights  Heights Block Surjectivity at Block apply 5df1ecab43d1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/IsWeightedHomogeneousSepBlock.lean#L50-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/IsWeightedHomogeneousSepBlock.lean#L50-L51

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

theorem P2M_GroundTheory_Heights__Heights_BlockSurjectivity_atBlock_apply_5df1ecab43d1 (k₀ : ι) (w : Cone (fun _ : Unit ↦ n k₀) ℂ) (q : MvPolynomial (Coord n) ℤ) :
    atBlock k₀ w q = map (evalBlock w) (sepBlock k₀ q) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«BlockSurjectivity».«atBlock_apply» := P2M_GroundTheory_Heights__Heights_BlockSurjectivity_atBlock_apply_5df1ecab43d1
