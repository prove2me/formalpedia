-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SegrePartition_sum_rho_22f6900690fe
-- name    : P2M_GroundTheory_Heights__Heights_SegrePartition_sum_rho_22f6900690fe
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T04:38:20.317388+00:00
-- url     : https://prove2.me/theorems/c2134dc2-5f43-407f-925d-e621657e98de
-- title:
--   P2 M Ground Theory Heights  Heights Segre Partition sum rho 22f6900690fe: P2 M Ground Theory Heights  Heights Segre Partition sum rho 22f6900690fe
-- statement:
--   The P2 M Ground Theory Heights  Heights Segre Partition sum rho 22f6900690fe construction uses the P2 M Ground Theory Heights  Heights Segre Partition sum rho 22f6900690fe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PSegrePartition.lean#L121-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PSegrePartition.lean#L121-L127

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

theorem P2M_GroundTheory_Heights__Heights_SegrePartition_sum_rho_22f6900690fe (hN : 0 < numIdx ι) (z : (Σ k, ι k) → ℂ) : ∑ i, rho (ι := ι) i z = 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SegrePartition».«sum_rho» := P2M_GroundTheory_Heights__Heights_SegrePartition_sum_rho_22f6900690fe
