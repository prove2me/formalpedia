-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SheetImageAreaSet_areaJacobian_comp_of_norm_5fbe9dbf23fd
-- name    : P2M_GroundTheory_Heights__Heights_SheetImageAreaSet_areaJacobian_comp_of_norm_5fbe9dbf23fd
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T04:37:24.090331+00:00
-- url     : https://prove2.me/theorems/9db643a0-b62c-49e0-8972-9bf91d4826e8
-- title:
--   P2 M Ground Theory Heights  Heights Sheet Image Area Set area Jacobian comp of norm 5fbe9dbf23fd: P2 M Ground Theory Heights  Heights Sheet Image Area Set area Jacobian comp of norm 5fbe9dbf23fd
-- statement:
--   The P2 M Ground Theory Heights  Heights Sheet Image Area Set area Jacobian comp of norm 5fbe9dbf23fd construction uses the P2 M Ground Theory Heights  Heights Sheet Image Area Set area Jacobian comp of norm 5fbe9dbf23fd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSheetImageAreaSetFrame.lean#L82-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSheetImageAreaSetFrame.lean#L82-L88

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StAreaMultiplicity
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PGraphAreaHolomorphic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetImageAreaSetFrame
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open Module
noncomputable section
open GroundTheory.Heights₂.Heights.SheetImageAreaSet

theorem P2M_GroundTheory_Heights__Heights_SheetImageAreaSet_areaJacobian_comp_of_norm_5fbe9dbf23fd {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (Q : F →ₗ[ℝ] F) (hQ : ∀ v, ‖Q v‖ = ‖v‖) (M : E →ₗ[ℝ] F) :
    areaJacobian (Q ∘ₗ M) = areaJacobian M := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SheetImageAreaSet».«areaJacobian_comp_of_norm» := P2M_GroundTheory_Heights__Heights_SheetImageAreaSet_areaJacobian_comp_of_norm_5fbe9dbf23fd
