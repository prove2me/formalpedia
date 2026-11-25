-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_BlockSurjectivity_exists_pow_prod_mem_759ee892cced
-- name    : P2M_GroundTheory_Heights__Heights_BlockSurjectivity_exists_pow_prod_mem_759ee892cced
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T00:17:20.186333+00:00
-- url     : https://prove2.me/theorems/81ed4db6-80ff-4a57-8fa1-e7d61127c03f
-- title:
--   P2 M Ground Theory Heights  Heights Block Surjectivity exists pow prod mem 759ee892cced: P2 M Ground Theory Heights  Heights Block Surjectivity exists pow prod mem 759ee892cced
-- statement:
--   The P2 M Ground Theory Heights  Heights Block Surjectivity exists pow prod mem 759ee892cced construction uses the P2 M Ground Theory Heights  Heights Block Surjectivity exists pow prod mem 759ee892cced property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/IsWeightedHomogeneousSepBlock.lean#L175-L208
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/IsWeightedHomogeneousSepBlock.lean#L175-L208

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

theorem P2M_GroundTheory_Heights__Heights_BlockSurjectivity_exists_pow_prod_mem_759ee892cced (P : ArithVariety n) (k₀ : ι) (w : Cone (fun _ : Unit ↦ n k₀) ℂ)
    (hw0 : w () ≠ 0) (hno : ∀ z ∈ P.points ℂ, z k₀ ≠ w ()) :
    ∃ N : ℕ, ∀ c : (k : ι) → Fin (n k + 1),
      (∏ k ∈ Finset.univ.erase k₀, (X ⟨k, c k⟩ : MvPolynomial (Coord n) ℂ)) ^ N ∈ fibreIdeal P k₀ w := by sorry

alias «GroundTheory».«Heights₂».«Heights».«BlockSurjectivity».«exists_pow_prod_mem» := P2M_GroundTheory_Heights__Heights_BlockSurjectivity_exists_pow_prod_mem_759ee892cced
