-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_BlockSurjectivity_withBlock_of_ne_12930e8adeee
-- name    : P2M_GroundTheory_Heights__Heights_BlockSurjectivity_withBlock_of_ne_12930e8adeee
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:49:48.210869+00:00
-- url     : https://prove2.me/theorems/80d61a15-0759-4fa2-b80b-0551b055a11d
-- title:
--   P2 M Ground Theory Heights  Heights Block Surjectivity with Block of ne 12930e8adeee: P2 M Ground Theory Heights  Heights Block Surjectivity with Block of ne 12930e8adeee
-- statement:
--   The P2 M Ground Theory Heights  Heights Block Surjectivity with Block of ne 12930e8adeee construction uses the P2 M Ground Theory Heights  Heights Block Surjectivity with Block of ne 12930e8adeee property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/IsWeightedHomogeneousSepBlock.lean#L62-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/IsWeightedHomogeneousSepBlock.lean#L62-L64

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

theorem P2M_GroundTheory_Heights__Heights_BlockSurjectivity_withBlock_of_ne_12930e8adeee {k₀ k : ι} (h : k ≠ k₀) (w₀ : Fin (n k₀ + 1) → ℂ) (x : Coord n → ℂ) :
    withBlock k₀ w₀ x k = fun i ↦ x ⟨k, i⟩ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«BlockSurjectivity».«withBlock_of_ne» := P2M_GroundTheory_Heights__Heights_BlockSurjectivity_withBlock_of_ne_12930e8adeee
