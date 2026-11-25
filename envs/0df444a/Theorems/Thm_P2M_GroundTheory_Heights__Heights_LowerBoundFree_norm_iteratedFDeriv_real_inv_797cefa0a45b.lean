-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_norm_iteratedFDeriv_real_inv_797cefa0a45b
-- name    : P2M_GroundTheory_Heights__Heights_LowerBoundFree_norm_iteratedFDeriv_real_inv_797cefa0a45b
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:28:23.933187+00:00
-- url     : https://prove2.me/theorems/16f8dc2c-6e8c-403f-8944-793e6078a8f1
-- title:
--   P2 M Ground Theory Heights  Heights Lower Bound Free norm iterated FDeriv real inv 797cefa0a45b: P2 M Ground Theory Heights  Heights Lower Bound Free norm iterated FDeriv real inv 797cefa0a45b
-- statement:
--   The P2 M Ground Theory Heights  Heights Lower Bound Free norm iterated FDeriv real inv 797cefa0a45b construction uses the P2 M Ground Theory Heights  Heights Lower Bound Free norm iterated FDeriv real inv 797cefa0a45b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/PInvDerivDecay.lean#L11-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/PInvDerivDecay.lean#L11-L17

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_StatementsInvDerivDecay
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_PInvDerivDecay
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
open Nat Set Filter Topology
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

theorem P2M_GroundTheory_Heights__Heights_LowerBoundFree_norm_iteratedFDeriv_real_inv_797cefa0a45b (k : ℕ) {z : ℂ} (hz : z ≠ 0) :
    ‖iteratedFDeriv ℝ k (Inv.inv : ℂ → ℂ) z‖ = k ! * (‖z‖ ^ (k + 1))⁻¹ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LowerBoundFree».«norm_iteratedFDeriv_real_inv» := P2M_GroundTheory_Heights__Heights_LowerBoundFree_norm_iteratedFDeriv_real_inv_797cefa0a45b
