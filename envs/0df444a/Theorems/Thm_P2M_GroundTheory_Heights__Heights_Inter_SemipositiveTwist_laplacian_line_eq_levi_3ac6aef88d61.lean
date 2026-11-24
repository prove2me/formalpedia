-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_SemipositiveTwist_laplacian_line_eq_levi_3ac6aef88d61
-- name    : P2M_GroundTheory_Heights__Heights_Inter_SemipositiveTwist_laplacian_line_eq_levi_3ac6aef88d61
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T01:33:46.457935+00:00
-- url     : https://prove2.me/theorems/c063a6fb-2f21-4751-a2f4-23bd92cd311f
-- title:
--   P2 M Ground Theory Heights  Heights Inter Semipositive Twist laplacian line eq levi 3ac6aef88d61: P2 M Ground Theory Heights  Heights Inter Semipositive Twist laplacian line eq levi 3ac6aef88d61
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Semipositive Twist laplacian line eq levi 3ac6aef88d61 construction uses the P2 M Ground Theory Heights  Heights Inter Semipositive Twist laplacian line eq levi 3ac6aef88d61 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PSemiPosTwist.lean#L94-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PSemiPosTwist.lean#L94-L115

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NoCommonComponentCoordinatesPlane
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StTorusInvLevi
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_ArithModel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ADensStC
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LeviOneEqLaplacianThm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PSemiPosTwist
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
open ReciprocityTheory.ChartRestriction.G.Geo Filter Topology InnerProductSpace Laplacian
open GroundTheory.Heights₂.Heights.Inter.SemipositiveTwist
set_option linter.unusedSectionVars false
variable {J : Type} [Fintype J]

theorem P2M_GroundTheory_Heights__Heights_Inter_SemipositiveTwist_laplacian_line_eq_levi_3ac6aef88d61 {φ : (J → ℂ) → ℝ} {z : J → ℂ} (hφ : ContDiffAt ℝ 2 φ z) (v : J → ℂ) :
    Δ (fun t : ℂ => φ (z + t • v)) 0 = 4 * ReciprocityTheory.AnForm.levi φ z v := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«SemipositiveTwist».«laplacian_line_eq_levi» := P2M_GroundTheory_Heights__Heights_Inter_SemipositiveTwist_laplacian_line_eq_levi_3ac6aef88d61
