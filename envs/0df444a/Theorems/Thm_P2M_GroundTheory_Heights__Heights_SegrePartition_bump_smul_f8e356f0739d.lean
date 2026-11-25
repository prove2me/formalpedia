-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SegrePartition_bump_smul_f8e356f0739d
-- name    : P2M_GroundTheory_Heights__Heights_SegrePartition_bump_smul_f8e356f0739d
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T04:37:39.60504+00:00
-- url     : https://prove2.me/theorems/ec06a3c5-89f1-46e9-848c-d99f1eaa438d
-- title:
--   P2 M Ground Theory Heights  Heights Segre Partition bump smul f8e356f0739d: P2 M Ground Theory Heights  Heights Segre Partition bump smul f8e356f0739d
-- statement:
--   The P2 M Ground Theory Heights  Heights Segre Partition bump smul f8e356f0739d construction uses the P2 M Ground Theory Heights  Heights Segre Partition bump smul f8e356f0739d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PSegrePartition.lean#L100-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PSegrePartition.lean#L100-L104

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

theorem P2M_GroundTheory_Heights__Heights_SegrePartition_bump_smul_f8e356f0739d (c : K → ℂ) (z : (Σ k, ι k) → ℂ) (hc : ∀ k, c k ≠ 0) (i : (k : K) → ι k) :
    bump (fun p => c p.1 * z p) i = bump z i := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SegrePartition».«bump_smul» := P2M_GroundTheory_Heights__Heights_SegrePartition_bump_smul_f8e356f0739d
