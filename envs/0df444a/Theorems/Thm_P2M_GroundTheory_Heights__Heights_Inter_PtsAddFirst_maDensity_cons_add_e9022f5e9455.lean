-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_PtsAddFirst_maDensity_cons_add_e9022f5e9455
-- name    : P2M_GroundTheory_Heights__Heights_Inter_PtsAddFirst_maDensity_cons_add_e9022f5e9455
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:43:13.94554+00:00
-- url     : https://prove2.me/theorems/ffc35bad-833c-4dbf-a9d8-fcc132a1c303
-- title:
--   P2 M Ground Theory Heights  Heights Inter Pts Add First ma Density cons add e9022f5e9455: P2 M Ground Theory Heights  Heights Inter Pts Add First ma Density cons add e9022f5e9455
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Pts Add First ma Density cons add e9022f5e9455 construction uses the P2 M Ground Theory Heights  Heights Inter Pts Add First ma Density cons add e9022f5e9455 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PPtsAddFirst.lean#L42-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PPtsAddFirst.lean#L42-L52

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSheet
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StPtsAddFirst
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PPtsAddFirst
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
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.ChartRestriction.G.Geo

theorem P2M_GroundTheory_Heights__Heights_Inter_PtsAddFirst_maDensity_cons_add_e9022f5e9455 {D : ℕ} (f g h : (Fin (D + 1) → ℂ) → ℝ)
    (ψ : Fin D → (Fin (D + 1) → ℂ) → ℝ) (y : Fin (D + 1) → ℂ)
    (hH : cxHessian h y = cxHessian f y + cxHessian g y) :
    maDensity (Fin.cons h ψ) y = maDensity (Fin.cons f ψ) y + maDensity (Fin.cons g ψ) y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«PtsAddFirst».«maDensity_cons_add» := P2M_GroundTheory_Heights__Heights_Inter_PtsAddFirst_maDensity_cons_add_e9022f5e9455
