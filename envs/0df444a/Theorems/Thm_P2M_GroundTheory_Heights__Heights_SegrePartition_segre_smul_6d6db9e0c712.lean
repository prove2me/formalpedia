-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SegrePartition_segre_smul_6d6db9e0c712
-- name    : P2M_GroundTheory_Heights__Heights_SegrePartition_segre_smul_6d6db9e0c712
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T04:37:36.147937+00:00
-- url     : https://prove2.me/theorems/b7e7dd0c-5f45-5af0-adb0-1464537cda5b
-- title:
--   P2 M Ground Theory Heights  Heights Segre Partition segre smul 6d6db9e0c712: P2 M Ground Theory Heights  Heights Segre Partition segre smul 6d6db9e0c712
-- statement:
--   The P2 M Ground Theory Heights  Heights Segre Partition segre smul 6d6db9e0c712 construction uses the P2 M Ground Theory Heights  Heights Segre Partition segre smul 6d6db9e0c712 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PSegrePartition.lean#L52-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PSegrePartition.lean#L52-L54

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

theorem P2M_GroundTheory_Heights__Heights_SegrePartition_segre_smul_6d6db9e0c712 (c : K → ℂ) (z : (Σ k, ι k) → ℂ) (i : (k : K) → ι k) :
    segre (fun p => c p.1 * z p) i = (∏ k, c k) * segre z i := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SegrePartition».«segre_smul» := P2M_GroundTheory_Heights__Heights_SegrePartition_segre_smul_6d6db9e0c712
