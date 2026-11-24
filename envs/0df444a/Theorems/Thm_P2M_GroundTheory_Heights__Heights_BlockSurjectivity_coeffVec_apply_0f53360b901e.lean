-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_BlockSurjectivity_coeffVec_apply_0f53360b901e
-- name    : P2M_GroundTheory_Heights__Heights_BlockSurjectivity_coeffVec_apply_0f53360b901e
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:57:58.625035+00:00
-- url     : https://prove2.me/theorems/d9c9b29e-1bbb-48a9-ba16-d71f5b223da2
-- title:
--   P2 M Ground Theory Heights  Heights Block Surjectivity coeff Vec apply 0f53360b901e: P2 M Ground Theory Heights  Heights Block Surjectivity coeff Vec apply 0f53360b901e
-- statement:
--   The P2 M Ground Theory Heights  Heights Block Surjectivity coeff Vec apply 0f53360b901e construction uses the P2 M Ground Theory Heights  Heights Block Surjectivity coeff Vec apply 0f53360b901e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/IsWeightedHomogeneousSepBlock.lean#L167-L168
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/IsWeightedHomogeneousSepBlock.lean#L167-L168

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

theorem P2M_GroundTheory_Heights__Heights_BlockSurjectivity_coeffVec_apply_0f53360b901e (M : Finset (Coord n →₀ ℕ)) (g : MvPolynomial (Coord n) ℂ) (μ : M) :
    coeffVec M g μ = coeff μ.1 g := by sorry

alias «GroundTheory».«Heights₂».«Heights».«BlockSurjectivity».«coeffVec_apply» := P2M_GroundTheory_Heights__Heights_BlockSurjectivity_coeffVec_apply_0f53360b901e
