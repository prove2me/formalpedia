-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SegrePartition_segreSq_nonneg_a601c8354dc1
-- name    : P2M_GroundTheory_Heights__Heights_SegrePartition_segreSq_nonneg_a601c8354dc1
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:33:53.217672+00:00
-- url     : https://prove2.me/theorems/d7e00ead-646d-406c-a08c-f8da9f37fc92
-- title:
--   P2 M Ground Theory Heights  Heights Segre Partition segre Sq nonneg a601c8354dc1: P2 M Ground Theory Heights  Heights Segre Partition segre Sq nonneg a601c8354dc1
-- statement:
--   The P2 M Ground Theory Heights  Heights Segre Partition segre Sq nonneg a601c8354dc1 construction uses the P2 M Ground Theory Heights  Heights Segre Partition segre Sq nonneg a601c8354dc1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PSegrePartition.lean#L30-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PSegrePartition.lean#L30-L31

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
omit [DecidableEq K] [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_SegrePartition_segreSq_nonneg_a601c8354dc1 (z : (Σ k, ι k) → ℂ) (i : (k : K) → ι k) : 0 ≤ segreSq z i := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SegrePartition».«segreSq_nonneg» := P2M_GroundTheory_Heights__Heights_SegrePartition_segreSq_nonneg_a601c8354dc1
