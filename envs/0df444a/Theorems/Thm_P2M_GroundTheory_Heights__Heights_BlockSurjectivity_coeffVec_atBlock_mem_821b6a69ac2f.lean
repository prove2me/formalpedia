-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_BlockSurjectivity_coeffVec_atBlock_mem_821b6a69ac2f
-- name    : P2M_GroundTheory_Heights__Heights_BlockSurjectivity_coeffVec_atBlock_mem_821b6a69ac2f
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T00:15:06.064244+00:00
-- url     : https://prove2.me/theorems/e670e6d5-3965-4989-9134-0b318dac8737
-- title:
--   P2 M Ground Theory Heights  Heights Block Surjectivity coeff Vec at Block mem 821b6a69ac2f: P2 M Ground Theory Heights  Heights Block Surjectivity coeff Vec at Block mem 821b6a69ac2f
-- statement:
--   The P2 M Ground Theory Heights  Heights Block Surjectivity coeff Vec at Block mem 821b6a69ac2f construction uses the P2 M Ground Theory Heights  Heights Block Surjectivity coeff Vec at Block mem 821b6a69ac2f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/IsWeightedHomogeneousSepBlock.lean#L255-L277
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/IsWeightedHomogeneousSepBlock.lean#L255-L277

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

theorem P2M_GroundTheory_Heights__Heights_BlockSurjectivity_coeffVec_atBlock_mem_821b6a69ac2f (P : ArithVariety n) (k₀ : ι) (w : Cone (fun _ : Unit ↦ n k₀) ℂ) (D : ℕ)
    {p : MvPolynomial (Coord n) ℤ} (hp : p ∈ P.ideal) :
    coeffVec (offMonos n k₀ D) (atBlock k₀ w p) ∈
      Submodule.span ℂ ((fun q ↦ coeffVec (offMonos n k₀ D) (atBlock k₀ w q)) '' homogIn n P k₀ D) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«BlockSurjectivity».«coeffVec_atBlock_mem» := P2M_GroundTheory_Heights__Heights_BlockSurjectivity_coeffVec_atBlock_mem_821b6a69ac2f
