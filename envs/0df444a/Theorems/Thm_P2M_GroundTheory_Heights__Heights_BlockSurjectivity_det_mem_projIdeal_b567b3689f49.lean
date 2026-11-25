-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_BlockSurjectivity_det_mem_projIdeal_b567b3689f49
-- name    : P2M_GroundTheory_Heights__Heights_BlockSurjectivity_det_mem_projIdeal_b567b3689f49
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T00:15:45.041268+00:00
-- url     : https://prove2.me/theorems/df92ed7c-d53d-472a-abeb-5972eaf4954b
-- title:
--   P2 M Ground Theory Heights  Heights Block Surjectivity det mem proj Ideal b567b3689f49: P2 M Ground Theory Heights  Heights Block Surjectivity det mem proj Ideal b567b3689f49
-- statement:
--   The P2 M Ground Theory Heights  Heights Block Surjectivity det mem proj Ideal b567b3689f49 construction uses the P2 M Ground Theory Heights  Heights Block Surjectivity det mem proj Ideal b567b3689f49 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/IsWeightedHomogeneousSepBlock.lean#L335-L389
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/IsWeightedHomogeneousSepBlock.lean#L335-L389

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

theorem P2M_GroundTheory_Heights__Heights_BlockSurjectivity_det_mem_projIdeal_b567b3689f49 (P : ArithVariety n) (k₀ : ι) (D : ℕ)
    (q : offMonos n k₀ D → MvPolynomial (Coord n) ℤ) (hq : ∀ i, q i ∈ homogIn n P k₀ D) :
    (Matrix.of fun i (μ : offMonos n k₀ D) ↦ coeff μ.1 (sepBlock k₀ (q i))).det ∈ P.projIdeal k₀ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«BlockSurjectivity».«det_mem_projIdeal» := P2M_GroundTheory_Heights__Heights_BlockSurjectivity_det_mem_projIdeal_b567b3689f49
