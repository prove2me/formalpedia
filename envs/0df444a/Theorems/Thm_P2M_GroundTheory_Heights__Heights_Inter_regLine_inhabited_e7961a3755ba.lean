-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_regLine_inhabited_e7961a3755ba
-- name    : P2M_GroundTheory_Heights__Heights_Inter_regLine_inhabited_e7961a3755ba
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T13:27:00.680443+00:00
-- url     : https://prove2.me/theorems/11cde644-6b90-5504-9ce7-100a90390a6d
-- title:
--   P2 M Ground Theory Heights  Heights Inter reg Line inhabited e7961a3755ba: P2 M Ground Theory Heights  Heights Inter reg Line inhabited e7961a3755ba
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter reg Line inhabited e7961a3755ba construction uses the P2 M Ground Theory Heights  Heights Inter reg Line inhabited e7961a3755ba property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/RegLine.lean#L104-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/RegLine.lean#L104-L111

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSheetA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NoCommonComponentCoordinatesPlane
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_RegLine
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
set_option linter.unusedSectionVars false

theorem P2M_GroundTheory_Heights__Heights_Inter_regLine_inhabited_e7961a3755ba :
    IsSmoothHerm (regLine (fsLine 3) (Xc 3 0) (isMultiHomog_planeCoordinate 0) 1) ∧
      (regLine (fsLine 3) (Xc 3 0) (isMultiHomog_planeCoordinate 0) 1).a = 0 ∧
      ∀ z ∈ mcPts (⊥ : Ideal (MRing (PBlk 3))), eval z (map (Int.castRingHom ℂ) (Xc 3 0)) ≠ 0 →
        logNorm (fsLine 3) (Xc 3 0) z ≤
          Real.log ((regLine (fsLine 3) (Xc 3 0) (isMultiHomog_planeCoordinate 0) 1).h z) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«regLine».«inhabited» := P2M_GroundTheory_Heights__Heights_Inter_regLine_inhabited_e7961a3755ba
