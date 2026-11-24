-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SegrePartition_segreSqSum_pos_5a693c0946e3
-- name    : P2M_GroundTheory_Heights__Heights_SegrePartition_segreSqSum_pos_5a693c0946e3
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:28:56.74121+00:00
-- url     : https://prove2.me/theorems/a093e759-0527-4f7d-9f72-841c736a1d1a
-- title:
--   P2 M Ground Theory Heights  Heights Segre Partition segre Sq Sum pos 5a693c0946e3: P2 M Ground Theory Heights  Heights Segre Partition segre Sq Sum pos 5a693c0946e3
-- statement:
--   The P2 M Ground Theory Heights  Heights Segre Partition segre Sq Sum pos 5a693c0946e3 construction uses the P2 M Ground Theory Heights  Heights Segre Partition segre Sq Sum pos 5a693c0946e3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PSegrePartition.lean#L44-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PSegrePartition.lean#L44-L48

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StSegrePartition
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PSegrePartition
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo (segre)
open GroundTheory.Heights₂.Heights.SegrePartition
variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_SegrePartition_segreSqSum_pos_5a693c0946e3 {z : (Σ k, ι k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) : 0 < segreSqSum z := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SegrePartition».«segreSqSum_pos» := P2M_GroundTheory_Heights__Heights_SegrePartition_segreSqSum_pos_5a693c0946e3
