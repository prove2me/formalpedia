-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_isSmoothHerm_tensor_ef70dcc84f59
-- name    : P2M_GroundTheory_Heights__Heights_Inter_isSmoothHerm_tensor_ef70dcc84f59
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:58:04.516143+00:00
-- url     : https://prove2.me/theorems/afde962e-6315-4962-8591-6829b8bcd6b9
-- title:
--   P2 M Ground Theory Heights  Heights Inter is Smooth Herm tensor ef70dcc84f59: P2 M Ground Theory Heights  Heights Inter is Smooth Herm tensor ef70dcc84f59
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter is Smooth Herm tensor ef70dcc84f59 construction uses the P2 M Ground Theory Heights  Heights Inter is Smooth Herm tensor ef70dcc84f59 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PThmAExpand.lean#L23-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PThmAExpand.lean#L23-L25

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_SymExp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsAntisym
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PThmAExpand
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I2
noncomputable section
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_Inter_isSmoothHerm_tensor_ef70dcc84f59 {A B : HermLine ι} (hA : IsSmoothHerm A) (hB : IsSmoothHerm B) :
    IsSmoothHerm (A.tensor B) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«isSmoothHerm_tensor» := P2M_GroundTheory_Heights__Heights_Inter_isSmoothHerm_tensor_ef70dcc84f59
