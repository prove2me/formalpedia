-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_BlockSurjectivity_le_weight_coordDeg_646f6af81263
-- name    : P2M_GroundTheory_Heights__Heights_BlockSurjectivity_le_weight_coordDeg_646f6af81263
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T00:18:04.706831+00:00
-- url     : https://prove2.me/theorems/b7c3c50d-b09c-4304-b8a4-aca5f3cb77bd
-- title:
--   P2 M Ground Theory Heights  Heights Block Surjectivity le weight coord Deg 646f6af81263: P2 M Ground Theory Heights  Heights Block Surjectivity le weight coord Deg 646f6af81263
-- statement:
--   The P2 M Ground Theory Heights  Heights Block Surjectivity le weight coord Deg 646f6af81263 construction uses the P2 M Ground Theory Heights  Heights Block Surjectivity le weight coord Deg 646f6af81263 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/IsWeightedHomogeneousSepBlock.lean#L138-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/IsWeightedHomogeneousSepBlock.lean#L138-L141

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

theorem P2M_GroundTheory_Heights__Heights_BlockSurjectivity_le_weight_coordDeg_646f6af81263 (μ : Coord n →₀ ℕ) (v : Coord n) :
    μ v ≤ Finsupp.weight (coordDeg n) μ v.1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«BlockSurjectivity».«le_weight_coordDeg» := P2M_GroundTheory_Heights__Heights_BlockSurjectivity_le_weight_coordDeg_646f6af81263
