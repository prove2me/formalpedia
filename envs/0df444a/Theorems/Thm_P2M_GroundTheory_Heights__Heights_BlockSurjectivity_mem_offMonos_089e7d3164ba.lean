-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_BlockSurjectivity_mem_offMonos_089e7d3164ba
-- name    : P2M_GroundTheory_Heights__Heights_BlockSurjectivity_mem_offMonos_089e7d3164ba
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:58:37.09511+00:00
-- url     : https://prove2.me/theorems/a751c7f6-15a6-439c-8d76-b4b3fa72e9df
-- title:
--   P2 M Ground Theory Heights  Heights Block Surjectivity mem off Monos 089e7d3164ba: P2 M Ground Theory Heights  Heights Block Surjectivity mem off Monos 089e7d3164ba
-- statement:
--   The P2 M Ground Theory Heights  Heights Block Surjectivity mem off Monos 089e7d3164ba construction uses the P2 M Ground Theory Heights  Heights Block Surjectivity mem off Monos 089e7d3164ba property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/IsWeightedHomogeneousSepBlock.lean#L151-L157
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/IsWeightedHomogeneousSepBlock.lean#L151-L157

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

theorem P2M_GroundTheory_Heights__Heights_BlockSurjectivity_mem_offMonos_089e7d3164ba {k₀ : ι} {D : ℕ} {μ : Coord n →₀ ℕ} :
    μ ∈ offMonos n k₀ D ↔ Finsupp.weight (coordDeg n) μ = offDeg k₀ D := by sorry

alias «GroundTheory».«Heights₂».«Heights».«BlockSurjectivity».«mem_offMonos» := P2M_GroundTheory_Heights__Heights_BlockSurjectivity_mem_offMonos_089e7d3164ba
