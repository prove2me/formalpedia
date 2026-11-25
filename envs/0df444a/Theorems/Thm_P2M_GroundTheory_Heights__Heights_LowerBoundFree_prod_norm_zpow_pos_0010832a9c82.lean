-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_prod_norm_zpow_pos_0010832a9c82
-- name    : P2M_GroundTheory_Heights__Heights_LowerBoundFree_prod_norm_zpow_pos_0010832a9c82
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:29:13.160769+00:00
-- url     : https://prove2.me/theorems/58d5af64-3925-4687-be0b-c9af8da2bfe1
-- title:
--   P2 M Ground Theory Heights  Heights Lower Bound Free prod norm zpow pos 0010832a9c82: P2 M Ground Theory Heights  Heights Lower Bound Free prod norm zpow pos 0010832a9c82
-- statement:
--   The P2 M Ground Theory Heights  Heights Lower Bound Free prod norm zpow pos 0010832a9c82 construction uses the P2 M Ground Theory Heights  Heights Lower Bound Free prod norm zpow pos 0010832a9c82 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/FrameDefinitions/Metric.lean#L148-L149
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/FrameDefinitions/Metric.lean#L148-L149

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_CoordinateIdeals_MemMCoordIdealOfAevalEqZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_FrameDefinitions_Metric
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_LowerBoundFree_prod_norm_zpow_pos_0010832a9c82 {c : K → ℂ} (hc : ∀ k, c k ≠ 0) (a : K → ℤ) : 0 < ∏ k, ‖c k‖ ^ a k := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LowerBoundFree».«prod_norm_zpow_pos» := P2M_GroundTheory_Heights__Heights_LowerBoundFree_prod_norm_zpow_pos_0010832a9c82
