-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_BlockSurjectivity_exists_point_over_42653c081ab0
-- name    : P2M_GroundTheory_Heights__Heights_BlockSurjectivity_exists_point_over_42653c081ab0
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T00:15:49.386016+00:00
-- url     : https://prove2.me/theorems/9ff67706-33c9-4ede-950c-52c470ed2e94
-- title:
--   P2 M Ground Theory Heights  Heights Block Surjectivity exists point over 42653c081ab0: P2 M Ground Theory Heights  Heights Block Surjectivity exists point over 42653c081ab0
-- statement:
--   The P2 M Ground Theory Heights  Heights Block Surjectivity exists point over 42653c081ab0 construction uses the P2 M Ground Theory Heights  Heights Block Surjectivity exists point over 42653c081ab0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/IsWeightedHomogeneousSepBlock.lean#L391-L431
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/IsWeightedHomogeneousSepBlock.lean#L391-L431

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

theorem P2M_GroundTheory_Heights__Heights_BlockSurjectivity_exists_point_over_42653c081ab0 (P : ArithVariety n) (k₀ : ι) (w : Cone (fun _ : Unit ↦ n k₀) ℂ)
    (hw : w ∈ conePoints (P.projIdeal k₀) ℂ) : ∃ z ∈ P.points ℂ, z k₀ = w () := by sorry

alias «GroundTheory».«Heights₂».«Heights».«BlockSurjectivity».«exists_point_over» := P2M_GroundTheory_Heights__Heights_BlockSurjectivity_exists_point_over_42653c081ab0
