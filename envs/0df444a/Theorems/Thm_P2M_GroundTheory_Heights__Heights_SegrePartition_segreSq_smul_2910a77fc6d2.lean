-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SegrePartition_segreSq_smul_2910a77fc6d2
-- name    : P2M_GroundTheory_Heights__Heights_SegrePartition_segreSq_smul_2910a77fc6d2
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:33:11.749796+00:00
-- url     : https://prove2.me/theorems/a20a0e7e-e390-4f36-8a74-045e3825eeae
-- title:
--   P2 M Ground Theory Heights  Heights Segre Partition segre Sq smul 2910a77fc6d2: P2 M Ground Theory Heights  Heights Segre Partition segre Sq smul 2910a77fc6d2
-- statement:
--   The P2 M Ground Theory Heights  Heights Segre Partition segre Sq smul 2910a77fc6d2 construction uses the P2 M Ground Theory Heights  Heights Segre Partition segre Sq smul 2910a77fc6d2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PSegrePartition.lean#L57-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PSegrePartition.lean#L57-L59

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

theorem P2M_GroundTheory_Heights__Heights_SegrePartition_segreSq_smul_2910a77fc6d2 (c : K → ℂ) (z : (Σ k, ι k) → ℂ) (i : (k : K) → ι k) :
    segreSq (fun p => c p.1 * z p) i = ‖∏ k, c k‖ ^ 2 * segreSq z i := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SegrePartition».«segreSq_smul» := P2M_GroundTheory_Heights__Heights_SegrePartition_segreSq_smul_2910a77fc6d2
