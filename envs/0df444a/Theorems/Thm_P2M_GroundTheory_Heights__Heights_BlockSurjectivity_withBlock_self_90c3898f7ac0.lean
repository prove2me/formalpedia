-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_BlockSurjectivity_withBlock_self_90c3898f7ac0
-- name    : P2M_GroundTheory_Heights__Heights_BlockSurjectivity_withBlock_self_90c3898f7ac0
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:49:37.55985+00:00
-- url     : https://prove2.me/theorems/77f26867-4f76-4cc8-8a6c-707d436ebed2
-- title:
--   P2 M Ground Theory Heights  Heights Block Surjectivity with Block self 90c3898f7ac0: P2 M Ground Theory Heights  Heights Block Surjectivity with Block self 90c3898f7ac0
-- statement:
--   The P2 M Ground Theory Heights  Heights Block Surjectivity with Block self 90c3898f7ac0 construction uses the P2 M Ground Theory Heights  Heights Block Surjectivity with Block self 90c3898f7ac0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/IsWeightedHomogeneousSepBlock.lean#L57-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/IsWeightedHomogeneousSepBlock.lean#L57-L59

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

theorem P2M_GroundTheory_Heights__Heights_BlockSurjectivity_withBlock_self_90c3898f7ac0 (k₀ : ι) (w₀ : Fin (n k₀ + 1) → ℂ) (x : Coord n → ℂ) :
    withBlock k₀ w₀ x k₀ = w₀ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«BlockSurjectivity».«withBlock_self» := P2M_GroundTheory_Heights__Heights_BlockSurjectivity_withBlock_self_90c3898f7ac0
