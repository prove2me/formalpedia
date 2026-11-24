-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SegrePartition_segreSqSum_smul_bbc7f323ad70
-- name    : P2M_GroundTheory_Heights__Heights_SegrePartition_segreSqSum_smul_bbc7f323ad70
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:33:14.572538+00:00
-- url     : https://prove2.me/theorems/96645c78-53e5-463e-b34d-97a14aa9a820
-- title:
--   P2 M Ground Theory Heights  Heights Segre Partition segre Sq Sum smul bbc7f323ad70: P2 M Ground Theory Heights  Heights Segre Partition segre Sq Sum smul bbc7f323ad70
-- statement:
--   The P2 M Ground Theory Heights  Heights Segre Partition segre Sq Sum smul bbc7f323ad70 construction uses the P2 M Ground Theory Heights  Heights Segre Partition segre Sq Sum smul bbc7f323ad70 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PSegrePartition.lean#L61-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PSegrePartition.lean#L61-L63

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

theorem P2M_GroundTheory_Heights__Heights_SegrePartition_segreSqSum_smul_bbc7f323ad70 (c : K → ℂ) (z : (Σ k, ι k) → ℂ) :
    segreSqSum (fun p => c p.1 * z p) = ‖∏ k, c k‖ ^ 2 * segreSqSum z := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SegrePartition».«segreSqSum_smul» := P2M_GroundTheory_Heights__Heights_SegrePartition_segreSqSum_smul_bbc7f323ad70
