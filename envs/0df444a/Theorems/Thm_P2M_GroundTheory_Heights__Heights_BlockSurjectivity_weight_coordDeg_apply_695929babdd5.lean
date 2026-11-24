-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_BlockSurjectivity_weight_coordDeg_apply_695929babdd5
-- name    : P2M_GroundTheory_Heights__Heights_BlockSurjectivity_weight_coordDeg_apply_695929babdd5
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:57:59.877244+00:00
-- url     : https://prove2.me/theorems/ca6f7466-209c-4413-9226-79da6953faf6
-- title:
--   P2 M Ground Theory Heights  Heights Block Surjectivity weight coord Deg apply 695929babdd5: P2 M Ground Theory Heights  Heights Block Surjectivity weight coord Deg apply 695929babdd5
-- statement:
--   The P2 M Ground Theory Heights  Heights Block Surjectivity weight coord Deg apply 695929babdd5 construction uses the P2 M Ground Theory Heights  Heights Block Surjectivity weight coord Deg apply 695929babdd5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/IsWeightedHomogeneousSepBlock.lean#L131-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/IsWeightedHomogeneousSepBlock.lean#L131-L136

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

theorem P2M_GroundTheory_Heights__Heights_BlockSurjectivity_weight_coordDeg_apply_695929babdd5 (μ : Coord n →₀ ℕ) (k : ι) :
    Finsupp.weight (coordDeg n) μ k = ∑ i, μ ⟨k, i⟩ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«BlockSurjectivity».«weight_coordDeg_apply» := P2M_GroundTheory_Heights__Heights_BlockSurjectivity_weight_coordDeg_apply_695929babdd5
