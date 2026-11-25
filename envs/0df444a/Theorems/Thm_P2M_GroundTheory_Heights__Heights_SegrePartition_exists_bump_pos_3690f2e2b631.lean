-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SegrePartition_exists_bump_pos_3690f2e2b631
-- name    : P2M_GroundTheory_Heights__Heights_SegrePartition_exists_bump_pos_3690f2e2b631
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:37:29.697014+00:00
-- url     : https://prove2.me/theorems/b6dc36a5-52bf-5ef0-a4a6-f877f311a8a0
-- title:
--   P2 M Ground Theory Heights  Heights Segre Partition exists bump pos 3690f2e2b631: P2 M Ground Theory Heights  Heights Segre Partition exists bump pos 3690f2e2b631
-- statement:
--   The P2 M Ground Theory Heights  Heights Segre Partition exists bump pos 3690f2e2b631 construction uses the P2 M Ground Theory Heights  Heights Segre Partition exists bump pos 3690f2e2b631 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PSegrePartition.lean#L65-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PSegrePartition.lean#L65-L85

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

theorem P2M_GroundTheory_Heights__Heights_SegrePartition_exists_bump_pos_3690f2e2b631 (hN : 0 < numIdx ι) {z : (Σ k, ι k) → ℂ} (hS : 0 < segreSqSum z) :
    ∃ j, 0 < bump z j := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SegrePartition».«exists_bump_pos» := P2M_GroundTheory_Heights__Heights_SegrePartition_exists_bump_pos_3690f2e2b631
