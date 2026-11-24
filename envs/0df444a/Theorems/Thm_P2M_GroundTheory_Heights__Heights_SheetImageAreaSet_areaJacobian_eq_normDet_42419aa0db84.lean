-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SheetImageAreaSet_areaJacobian_eq_normDet_42419aa0db84
-- name    : P2M_GroundTheory_Heights__Heights_SheetImageAreaSet_areaJacobian_eq_normDet_42419aa0db84
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:32:29.213149+00:00
-- url     : https://prove2.me/theorems/97bd66dc-7bed-43ab-bc5c-7007cdc660e3
-- title:
--   P2 M Ground Theory Heights  Heights Sheet Image Area Set area Jacobian eq norm Det 42419aa0db84: P2 M Ground Theory Heights  Heights Sheet Image Area Set area Jacobian eq norm Det 42419aa0db84
-- statement:
--   The P2 M Ground Theory Heights  Heights Sheet Image Area Set area Jacobian eq norm Det 42419aa0db84 construction uses the P2 M Ground Theory Heights  Heights Sheet Image Area Set area Jacobian eq norm Det 42419aa0db84 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSheetImageAreaSetFrame.lean#L75-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSheetImageAreaSetFrame.lean#L75-L80

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

theorem P2M_GroundTheory_Heights__Heights_SheetImageAreaSet_areaJacobian_eq_normDet_42419aa0db84 {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (M : E →ₗ[ℝ] F) : areaJacobian M = M.normDet := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SheetImageAreaSet».«areaJacobian_eq_normDet» := P2M_GroundTheory_Heights__Heights_SheetImageAreaSet_areaJacobian_eq_normDet_42419aa0db84
