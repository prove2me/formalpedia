-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_fsPotPlane_eq_67515711d37d
-- name    : P2M_GroundTheory_Heights__Heights_LowerBoundFree_fsPotPlane_eq_67515711d37d
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:28:46.994237+00:00
-- url     : https://prove2.me/theorems/1837a89c-8a63-40e9-ae63-935d1b5fcce2
-- title:
--   P2 M Ground Theory Heights  Heights Lower Bound Free fs Pot Plane eq 67515711d37d: P2 M Ground Theory Heights  Heights Lower Bound Free fs Pot Plane eq 67515711d37d
-- statement:
--   The P2 M Ground Theory Heights  Heights Lower Bound Free fs Pot Plane eq 67515711d37d construction uses the P2 M Ground Theory Heights  Heights Lower Bound Free fs Pot Plane eq 67515711d37d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/StatementsLaplacianLogGrowth.lean#L21-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/StatementsLaplacianLogGrowth.lean#L21-L30

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_StatementsLaplacianLogGrowth
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
open InnerProductSpace Laplacian Real

theorem P2M_GroundTheory_Heights__Heights_LowerBoundFree_fsPotPlane_eq_67515711d37d {y : ℂ} (hy : 1⁻¹ < ‖y‖) : fsPotPlane y = 1 * Real.log ‖y‖ + fsPotPlane y⁻¹ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LowerBoundFree».«fsPotPlane_eq» := P2M_GroundTheory_Heights__Heights_LowerBoundFree_fsPotPlane_eq_67515711d37d
