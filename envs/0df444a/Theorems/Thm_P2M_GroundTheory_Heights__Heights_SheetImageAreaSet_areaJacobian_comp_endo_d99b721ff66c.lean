-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SheetImageAreaSet_areaJacobian_comp_endo_d99b721ff66c
-- name    : P2M_GroundTheory_Heights__Heights_SheetImageAreaSet_areaJacobian_comp_endo_d99b721ff66c
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T04:37:45.955229+00:00
-- url     : https://prove2.me/theorems/cc0d392c-56b6-415e-a93c-7321a0702aca
-- title:
--   P2 M Ground Theory Heights  Heights Sheet Image Area Set area Jacobian comp endo d99b721ff66c: P2 M Ground Theory Heights  Heights Sheet Image Area Set area Jacobian comp endo d99b721ff66c
-- statement:
--   The P2 M Ground Theory Heights  Heights Sheet Image Area Set area Jacobian comp endo d99b721ff66c construction uses the P2 M Ground Theory Heights  Heights Sheet Image Area Set area Jacobian comp endo d99b721ff66c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSheetImageAreaSetFrame.lean#L90-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSheetImageAreaSetFrame.lean#L90-L95

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

theorem P2M_GroundTheory_Heights__Heights_SheetImageAreaSet_areaJacobian_comp_endo_d99b721ff66c {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (M : E →ₗ[ℝ] F) (T : E →ₗ[ℝ] E) :
    areaJacobian (M ∘ₗ T) = areaJacobian M * |LinearMap.det T| := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SheetImageAreaSet».«areaJacobian_comp_endo» := P2M_GroundTheory_Heights__Heights_SheetImageAreaSet_areaJacobian_comp_endo_d99b721ff66c
