-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SegrePartition_isDegZeroSmooth_rho_f620d4c5f71e
-- name    : P2M_GroundTheory_Heights__Heights_SegrePartition_isDegZeroSmooth_rho_f620d4c5f71e
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:37:29.082798+00:00
-- url     : https://prove2.me/theorems/b61f4f32-869d-4eff-b431-64ad134283c0
-- title:
--   P2 M Ground Theory Heights  Heights Segre Partition is Deg Zero Smooth rho f620d4c5f71e: P2 M Ground Theory Heights  Heights Segre Partition is Deg Zero Smooth rho f620d4c5f71e
-- statement:
--   The P2 M Ground Theory Heights  Heights Segre Partition is Deg Zero Smooth rho f620d4c5f71e construction uses the P2 M Ground Theory Heights  Heights Segre Partition is Deg Zero Smooth rho f620d4c5f71e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PSegrePartition.lean#L106-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PSegrePartition.lean#L106-L119

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

theorem P2M_GroundTheory_Heights__Heights_SegrePartition_isDegZeroSmooth_rho_f620d4c5f71e (hN : 0 < numIdx ι) (i : (k : K) → ι k) :
    IsDegZeroSmooth (rho (ι := ι) i) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SegrePartition».«isDegZeroSmooth_rho» := P2M_GroundTheory_Heights__Heights_SegrePartition_isDegZeroSmooth_rho_f620d4c5f71e
