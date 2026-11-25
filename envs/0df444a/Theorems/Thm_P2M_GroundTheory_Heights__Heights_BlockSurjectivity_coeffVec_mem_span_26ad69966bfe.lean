-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_BlockSurjectivity_coeffVec_mem_span_26ad69966bfe
-- name    : P2M_GroundTheory_Heights__Heights_BlockSurjectivity_coeffVec_mem_span_26ad69966bfe
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T00:16:15.409769+00:00
-- url     : https://prove2.me/theorems/17a0f354-e2d6-4adf-936d-7b883a2da617
-- title:
--   P2 M Ground Theory Heights  Heights Block Surjectivity coeff Vec mem span 26ad69966bfe: P2 M Ground Theory Heights  Heights Block Surjectivity coeff Vec mem span 26ad69966bfe
-- statement:
--   The P2 M Ground Theory Heights  Heights Block Surjectivity coeff Vec mem span 26ad69966bfe construction uses the P2 M Ground Theory Heights  Heights Block Surjectivity coeff Vec mem span 26ad69966bfe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/IsWeightedHomogeneousSepBlock.lean#L312-L333
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/IsWeightedHomogeneousSepBlock.lean#L312-L333

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

theorem P2M_GroundTheory_Heights__Heights_BlockSurjectivity_coeffVec_mem_span_26ad69966bfe (P : ArithVariety n) (k₀ : ι) (w : Cone (fun _ : Unit ↦ n k₀) ℂ) (D : ℕ)
    {g : MvPolynomial (Coord n) ℂ} (hg : g ∈ fibreIdeal P k₀ w) :
    coeffVec (offMonos n k₀ D) g ∈
      Submodule.span ℂ ((fun q ↦ coeffVec (offMonos n k₀ D) (atBlock k₀ w q)) '' homogIn n P k₀ D) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«BlockSurjectivity».«coeffVec_mem_span» := P2M_GroundTheory_Heights__Heights_BlockSurjectivity_coeffVec_mem_span_26ad69966bfe
