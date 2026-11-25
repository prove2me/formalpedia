-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SegrePartition_rho_eq_zero_f7e1fc5f243f
-- name    : P2M_GroundTheory_Heights__Heights_SegrePartition_rho_eq_zero_f7e1fc5f243f
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T04:38:10.30052+00:00
-- url     : https://prove2.me/theorems/929245dd-cc1d-416e-85c3-5babf1460770
-- title:
--   P2 M Ground Theory Heights  Heights Segre Partition rho eq zero f7e1fc5f243f: P2 M Ground Theory Heights  Heights Segre Partition rho eq zero f7e1fc5f243f
-- statement:
--   The P2 M Ground Theory Heights  Heights Segre Partition rho eq zero f7e1fc5f243f construction uses the P2 M Ground Theory Heights  Heights Segre Partition rho eq zero f7e1fc5f243f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PSegrePartition.lean#L129-L158
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PSegrePartition.lean#L129-L158

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

theorem P2M_GroundTheory_Heights__Heights_SegrePartition_rho_eq_zero_f7e1fc5f243f (hN : 0 < numIdx ι) (i : (k : K) → ι k) (z : (Σ k, ι k) → ℂ)
    (h : ‖segre z i‖ < (Real.sqrt (2 * numIdx ι))⁻¹ * ‖segre z‖) : rho i z = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SegrePartition».«rho_eq_zero» := P2M_GroundTheory_Heights__Heights_SegrePartition_rho_eq_zero_f7e1fc5f243f
