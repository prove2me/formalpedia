-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_BlockSurjectivity_coeffVec_mul_atBlock_mem_f996223746d1
-- name    : P2M_GroundTheory_Heights__Heights_BlockSurjectivity_coeffVec_mul_atBlock_mem_f996223746d1
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T00:18:01.157808+00:00
-- url     : https://prove2.me/theorems/250b9d4f-e197-40b6-83c6-e912bdf92bfa
-- title:
--   P2 M Ground Theory Heights  Heights Block Surjectivity coeff Vec mul at Block mem f996223746d1: P2 M Ground Theory Heights  Heights Block Surjectivity coeff Vec mul at Block mem f996223746d1
-- statement:
--   The P2 M Ground Theory Heights  Heights Block Surjectivity coeff Vec mul at Block mem f996223746d1 construction uses the P2 M Ground Theory Heights  Heights Block Surjectivity coeff Vec mul at Block mem f996223746d1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/IsWeightedHomogeneousSepBlock.lean#L279-L310
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/IsWeightedHomogeneousSepBlock.lean#L279-L310

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

theorem P2M_GroundTheory_Heights__Heights_BlockSurjectivity_coeffVec_mul_atBlock_mem_f996223746d1 (P : ArithVariety n) (k₀ : ι) (w : Cone (fun _ : Unit ↦ n k₀) ℂ)
    (D : ℕ) (h : MvPolynomial (Coord n) ℂ) :
    ∀ p ∈ P.ideal, coeffVec (offMonos n k₀ D) (h * atBlock k₀ w p) ∈
      Submodule.span ℂ ((fun q ↦ coeffVec (offMonos n k₀ D) (atBlock k₀ w q)) '' homogIn n P k₀ D) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«BlockSurjectivity».«coeffVec_mul_atBlock_mem» := P2M_GroundTheory_Heights__Heights_BlockSurjectivity_coeffVec_mul_atBlock_mem_f996223746d1
